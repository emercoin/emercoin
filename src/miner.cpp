// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <miner.h>

#include <amount.h>
#include <chain.h>
#include <chainparams.h>
#include <coins.h>
#include <consensus/consensus.h>
#include <consensus/merkle.h>
#include <consensus/tx_verify.h>
#include <consensus/validation.h>
#include <policy/feerate.h>
#include <policy/policy.h>
#include <pow.h>
#include <primitives/transaction.h>
#include <script/standard.h>
#include <timedata.h>
#include <util/moneystr.h>
#include <util/system.h>
#include <util/validation.h>

#include <wallet/wallet.h>
#include <wallet/coincontrol.h>
#include <warnings.h>
#include <net.h>
#include <kernel.h>

#include <algorithm>
#include <queue>
#include <utility>

#include <stack>

int64_t nLastCoinStakeSearchInterval = 0;

// Located in kernel.cpp
extern CAmount GetQuantProtection();

int64_t UpdateTime(CBlockHeader* pblock, const Consensus::Params& consensusParams, const CBlockIndex* pindexPrev)
{
    int64_t nOldTime = pblock->nTime;
    int64_t nNewTime = std::max(pindexPrev->GetMedianTimePast()+1, GetAdjustedTime());

    if (nOldTime < nNewTime)
        pblock->nTime = nNewTime;

    return nNewTime - nOldTime;
}

BlockAssembler::Options::Options() {
    blockMinFeeRate = CFeeRate(DEFAULT_BLOCK_MIN_TX_FEE);
    nBlockMaxWeight = DEFAULT_BLOCK_MAX_WEIGHT;
}

BlockAssembler::BlockAssembler(const CChainParams& params, const Options& options) : chainparams(params)
{
    blockMinFeeRate = options.blockMinFeeRate;
    // Limit weight to between 4K and MAX_BLOCK_WEIGHT-4K for sanity:
    nBlockMaxWeight = std::max<size_t>(4000, std::min<size_t>(MAX_BLOCK_WEIGHT - 4000, options.nBlockMaxWeight));
}

static BlockAssembler::Options DefaultOptions()
{
    // Block resource limits
    // If -blockmaxweight is not given, limit to DEFAULT_BLOCK_MAX_WEIGHT
    BlockAssembler::Options options;
    options.nBlockMaxWeight = gArgs.GetArg("-blockmaxweight", DEFAULT_BLOCK_MAX_WEIGHT);
    CAmount n = 0;
    if (gArgs.IsArgSet("-blockmintxfee") && ParseMoney(gArgs.GetArg("-blockmintxfee", ""), n)) {
        options.blockMinFeeRate = CFeeRate(n);
    } else {
        options.blockMinFeeRate = CFeeRate(DEFAULT_BLOCK_MIN_TX_FEE);
    }
    return options;
}

BlockAssembler::BlockAssembler(const CChainParams& params) : BlockAssembler(params, DefaultOptions()) {}

void BlockAssembler::resetBlock()
{
    inBlock.clear();

    // Reserve space for coinbase tx
    nBlockWeight = 4000;
    nBlockSigOpsCost = 400;
    // These counters do not include coinbase tx
    nBlockTx = 0;
    nFees = 0;
}

Optional<int64_t> BlockAssembler::m_last_block_num_txs{nullopt};
Optional<int64_t> BlockAssembler::m_last_block_weight{nullopt};

std::unique_ptr<CBlockTemplate> BlockAssembler::CreateNewBlock(const CScript& scriptPubKeyIn, CWallet* pwallet, bool* pfPoSCancel)
{
    int64_t nTimeStart = GetTimeMicros();

    resetBlock();

    pblocktemplate.reset(new CBlockTemplate());

    if(!pblocktemplate.get())
        return nullptr;
    pblock = &pblocktemplate->block; // pointer for convenience

    // Create coinbase transaction.
    CMutableTransaction coinbaseTx;
    coinbaseTx.vin.resize(1);
    coinbaseTx.vin[0].prevout.SetNull();
    coinbaseTx.vout.resize(1);
    coinbaseTx.vout[0].scriptPubKey = scriptPubKeyIn;

    // Add dummy coinbase tx as first transaction
    pblock->vtx.emplace_back();
    pblocktemplate->vTxFees.push_back(-1); // updated at end
    pblocktemplate->vTxSigOpsCost.push_back(-1); // updated at end

    // ppcoin: if coinstake available add coinstake tx
    static int64_t nLastCoinStakeSearchTime = GetAdjustedTime();  // only initialized at startup

    LOCK(cs_main);
    CBlockIndex* pindexPrev = ::ChainActive().Tip();
    assert(pindexPrev != nullptr);

    // attemp to find a coinstake
    if (pwallet) {
        *pfPoSCancel = true;
        pblock->nBits = GetNextTargetRequired(pindexPrev, true, chainparams.GetConsensus());
        CMutableTransaction txCoinStake;
        int64_t nSearchTime = txCoinStake.nTime; // search to current time
        if (nSearchTime > nLastCoinStakeSearchTime) {
            if (CreateCoinStake(pwallet, pblock->nBits, nSearchTime-nLastCoinStakeSearchTime, txCoinStake)) {
                // make sure coinstake would meet timestamp protocol
                if (txCoinStake.nTime >= std::max(pindexPrev->GetMedianTimePast()+1, pindexPrev->GetBlockTime() - nMaxClockDrift)) {
                    // as it would be the same as the block timestamp
                    coinbaseTx.vout[0].nValue = 0;
                    coinbaseTx.vout[0].scriptPubKey.clear();
                    coinbaseTx.nTime = txCoinStake.nTime;
                    pblock->vtx.push_back(MakeTransactionRef(CTransaction(txCoinStake)));
                    pblock->nFlags |= BLOCK_PROOF_OF_STAKE;
                    *pfPoSCancel = false;
                }
            }
            nLastCoinStakeSearchInterval = nSearchTime - nLastCoinStakeSearchTime;
            nLastCoinStakeSearchTime = nSearchTime;
        }
        if (*pfPoSCancel)
            return nullptr; // emercoin: there is no point to continue if we failed to create coinstake
    }
    else
        pblock->nBits = GetNextTargetRequired(pindexPrev, false, chainparams.GetConsensus());

    LOCK(mempool.cs);

    nHeight = pindexPrev->nHeight + 1;

    pblock->SetBlockVersion(gArgs.GetArg("-blockversion", pblock->nVersion));

    pblock->nTime = GetAdjustedTime();
    const int64_t nMedianTimePast = pindexPrev->GetMedianTimePast();

    nLockTimeCutoff = (STANDARD_LOCKTIME_VERIFY_FLAGS & LOCKTIME_MEDIAN_TIME_PAST)
                       ? nMedianTimePast
                       : pblock->GetBlockTime();

    // Decide whether to include witness transactions
    // This is only needed in case the witness softfork activation is reverted
    // (which would require a very deep reorganization).
    // Note that the mempool would accept transactions with witness data before
    // IsWitnessEnabled, but we would only ever mine blocks after IsWitnessEnabled
    // unless there is a massive block reorganization with the witness softfork
    // not activated.
    // TODO: replace this with a call to main to assess validity of a mempool
    // transaction (which in most cases can be a no-op).

    addTxs();

    int64_t nTime1 = GetTimeMicros();

    m_last_block_num_txs = nBlockTx;
    m_last_block_weight = nBlockWeight;

    // Compute final coinbase transaction.
    if (pblock->IsProofOfWork()) {
        // Add quant protection here
        CAmount nQuantProtection = GetQuantProtection();
        CAmount nReward = GetProofOfWorkReward(pblock->nBits);
        CAmount vout0;
        if(nQuantProtection < 0)
            vout0 = -nQuantProtection;
        else
        if(nQuantProtection > 0)
            vout0 = GetRand(nQuantProtection) / TX_DP_AMOUNT * TX_DP_AMOUNT;
        else
            vout0 = nReward;

        if(vout0 < MIN_TXOUT_AMOUNT)
            vout0 = MIN_TXOUT_AMOUNT;
        if(vout0 > nReward)
            vout0 = nReward;

        if(vout0 <= nReward - MIN_TXOUT_AMOUNT) {
            ReserveDestination reservedest(pwallet);
            CTxDestination dest;
            if (reservedest.GetReservedDestination(OutputType::BECH32, dest, true)) {
                coinbaseTx.vout.push_back(CTxOut(nReward - vout0, GetScriptForDestination(dest)));
                reservedest.KeepDestination();
            } else
                vout0 = nReward; // Revert back enrire reward to p2pk
        }
        coinbaseTx.vout[0].nValue = vout0;
    }

    coinbaseTx.vin[0].scriptSig = CScript() << nHeight << OP_0;
    pblock->vtx[0] = MakeTransactionRef(std::move(coinbaseTx));
    pblocktemplate->vchCoinbaseCommitment = GenerateCoinbaseCommitment(*pblock, pindexPrev, chainparams.GetConsensus());
    pblocktemplate->vTxFees[0] = -nFees;

    LogPrintf("CreateNewBlock(): block weight: %u txs: %u fees: %ld sigops %d\n", GetBlockWeight(*pblock), nBlockTx, nFees, nBlockSigOpsCost);

    // Fill in header
    pblock->hashPrevBlock  = pindexPrev->GetBlockHash();
    if (pblock->IsProofOfStake())
        pblock->nTime      = pblock->vtx[1]->nTime; //same as coinstake timestamp
    pblock->nTime          = std::max(pindexPrev->GetMedianTimePast()+1, pblock->GetMaxTransactionTime());
    pblock->nTime          = std::max(pblock->GetBlockTime(), pindexPrev->GetBlockTime() - nMaxClockDrift);
    if (pblock->IsProofOfWork())
        UpdateTime(pblock, chainparams.GetConsensus(), pindexPrev);
    pblock->nNonce         = 0;
    pblocktemplate->vTxSigOpsCost[0] = WITNESS_SCALE_FACTOR * GetLegacySigOpCount(*pblock->vtx[0]);

    CValidationState state;
    if (!TestBlockValidity(state, chainparams, *pblock, pindexPrev, false, false, false)) {   // emercoin: we do not check block signature here, since we did not sign it yet
        throw std::runtime_error(strprintf("%s: TestBlockValidity failed: %s", __func__, FormatStateMessage(state)));
    }
    int64_t nTime2 = GetTimeMicros();

    LogPrint(BCLog::BENCH, "CreateNewBlock() txs: %.2fms, validity: %.2fms (total %.2fms)\n", 0.001 * (nTime1 - nTimeStart), 0.001 * (nTime2 - nTime1), 0.001 * (nTime2 - nTimeStart));

    return std::move(pblocktemplate);
}

void BlockAssembler::onlyUnconfirmed(CTxMemPool::setEntries& testSet)
{
    for (CTxMemPool::setEntries::iterator iit = testSet.begin(); iit != testSet.end(); ) {
        // Only test txs not already in the block
        if (inBlock.count(*iit)) {
            testSet.erase(iit++);
        }
        else {
            iit++;
        }
    }
}
#if 0
bool BlockAssembler::TestPackage(uint64_t packageSize, int64_t packageSigOpsCost) const
{
    // TODO: switch to weight-based accounting for packages instead of vsize-based accounting.
    if (nBlockWeight + WITNESS_SCALE_FACTOR * packageSize >= nBlockMaxWeight)
        return false;
    if (nBlockSigOpsCost + packageSigOpsCost >= MAX_BLOCK_SIGOPS_COST)
        return false;
    return true;
}

// Perform transaction-level checks before adding to block:
// - transaction finality (locktime)
// - premature witness (in case segwit transactions are added to mempool before
//   segwit activation)
bool BlockAssembler::TestPackageTransactions(const CTxMemPool::setEntries& package)
{
    for (CTxMemPool::txiter it : package) {
        if (!IsFinalTx(it->GetTx(), nHeight, nLockTimeCutoff))
            return false;
        if (!fIncludeWitness && it->GetTx().HasWitness())
            return false;

        // ppcoin: timestamp limit
        if (it->GetTx().nTime > GetAdjustedTime() || (pblock->IsProofOfStake() && it->GetTx().nTime > pblock->vtx[1]->nTime))
            return false;
    }
    return true;
}
#endif

bool BlockAssembler::AddToBlock(CTxMemPool::txiter iter)
{
    size_t new_block_weight = nBlockWeight + iter->GetTxWeight();
    if(new_block_weight >= nBlockMaxWeight)
        return false; // Block is full, do not add TX
    pblock->vtx.emplace_back(iter->GetSharedTx());
    pblocktemplate->vTxFees.push_back(iter->GetFee());
    pblocktemplate->vTxSigOpsCost.push_back(iter->GetSigOpCost());
    nBlockWeight = new_block_weight;
    ++nBlockTx;
    nBlockSigOpsCost += iter->GetSigOpCost();
    nFees += iter->GetFee();
    inBlock.insert(iter);

    bool fPrintPriority = gArgs.GetBoolArg("-printpriority", DEFAULT_PRINTPRIORITY);
    if (fPrintPriority) {
        LogPrintf("fee %s txid %s\n",
                  CFeeRate(iter->GetModifiedFee(), iter->GetTxSize()).ToString(),
                  iter->GetTx().GetHash().ToString());
    }
    return true;
}

int BlockAssembler::UpdatePackagesForAdded(const CTxMemPool::setEntries& alreadyAdded,
        indexed_modified_transaction_set &mapModifiedTx)
{
    int nDescendantsUpdated = 0;
    for (CTxMemPool::txiter it : alreadyAdded) {
        CTxMemPool::setEntries descendants;
        mempool.CalculateDescendants(it, descendants);
        // Insert all descendants (not yet in block) into the modified set
        for (CTxMemPool::txiter desc : descendants) {
            if (alreadyAdded.count(desc))
                continue;
            ++nDescendantsUpdated;
            modtxiter mit = mapModifiedTx.find(desc);
            if (mit == mapModifiedTx.end()) {
                CTxMemPoolModifiedEntry modEntry(desc);
                modEntry.nSizeWithAncestors -= it->GetTxSize();
                modEntry.nModFeesWithAncestors -= it->GetModifiedFee();
                modEntry.nSigOpCostWithAncestors -= it->GetSigOpCost();
                mapModifiedTx.insert(modEntry);
            } else {
                mapModifiedTx.modify(mit, update_for_parent_inclusion(it));
            }
        }
    }
    return nDescendantsUpdated;
}

// Skip entries in mapTx that are already in a block or are present
// in mapModifiedTx (which implies that the mapTx ancestor state is
// stale due to ancestor inclusion in the block)
// Also skip transactions that we've already failed to add. This can happen if
// we consider a transaction in mapModifiedTx and it fails: we can then
// potentially consider it again while walking mapTx.  It's currently
// guaranteed to fail again, but as a belt-and-suspenders check we put it in
// failedTx and avoid re-evaluation, since the re-evaluation would be using
// cached size/sigops/fee values that are not actually correct.
bool BlockAssembler::SkipMapTxEntry(CTxMemPool::txiter it, indexed_modified_transaction_set &mapModifiedTx, CTxMemPool::setEntries &failedTx)
{
    assert (it != mempool.mapTx.end());
    return mapModifiedTx.count(it) || inBlock.count(it) || failedTx.count(it);
}

void BlockAssembler::SortForBlock(const CTxMemPool::setEntries& package, std::vector<CTxMemPool::txiter>& sortedEntries)
{
    // Sort package by ancestor count
    // If a transaction A depends on transaction B, then A's ancestor count
    // must be greater than B's.  So this is sufficient to validly order the
    // transactions for block inclusion.
    sortedEntries.clear();
    sortedEntries.insert(sortedEntries.begin(), package.begin(), package.end());
    std::sort(sortedEntries.begin(), sortedEntries.end(), CompareTxIterByAncestorCount());
}
#if 0
/// Oleg: anyway, not used
// This transaction selection algorithm orders the mempool based
// on feerate of a transaction including all unconfirmed ancestors.
// Since we don't remove transactions from the mempool as we select them
// for block inclusion, we need an alternate method of updating the feerate
// of a transaction with its not-yet-selected ancestors as we go.
// This is accomplished by walking the in-mempool descendants of selected
// transactions and storing a temporary modified state in mapModifiedTxs.
// Each time through the loop, we compare the best transaction in
// mapModifiedTxs with the next transaction in the mempool to decide what
// transaction package to work on next.
void BlockAssembler::addPackageTxs(int &nPackagesSelected, int &nDescendantsUpdated)
{
    // mapModifiedTx will store sorted packages after they are modified
    // because some of their txs are already in the block
    indexed_modified_transaction_set mapModifiedTx;
    // Keep track of entries that failed inclusion, to avoid duplicate work
    CTxMemPool::setEntries failedTx;

    // Start by adding all descendants of previously added txs to mapModifiedTx
    // and modifying them for their already included ancestors
    UpdatePackagesForAdded(inBlock, mapModifiedTx);

    CTxMemPool::indexed_transaction_set::index<ancestor_score>::type::iterator mi = mempool.mapTx.get<ancestor_score>().begin();
    CTxMemPool::txiter iter;

    // Limit the number of attempts to add transactions to the block when it is
    // close to full; this is just a simple heuristic to finish quickly if the
    // mempool has a lot of entries.
    const int64_t MAX_CONSECUTIVE_FAILURES = 1000;
    int64_t nConsecutiveFailed = 0;

    while (mi != mempool.mapTx.get<ancestor_score>().end() || !mapModifiedTx.empty())
    {
        // First try to find a new transaction in mapTx to evaluate.
        if (mi != mempool.mapTx.get<ancestor_score>().end() &&
                SkipMapTxEntry(mempool.mapTx.project<0>(mi), mapModifiedTx, failedTx)) {
            ++mi;
            continue;
        }

        // Now that mi is not stale, determine which transaction to evaluate:
        // the next entry from mapTx, or the best from mapModifiedTx?
        bool fUsingModified = false;

        modtxscoreiter modit = mapModifiedTx.get<ancestor_score>().begin();
        if (mi == mempool.mapTx.get<ancestor_score>().end()) {
            // We're out of entries in mapTx; use the entry from mapModifiedTx
            iter = modit->iter;
            fUsingModified = true;
        } else {
            // Try to compare the mapTx entry to the mapModifiedTx entry
            iter = mempool.mapTx.project<0>(mi);
            if (modit != mapModifiedTx.get<ancestor_score>().end() &&
                    CompareTxMemPoolEntryByAncestorFee()(*modit, CTxMemPoolModifiedEntry(iter))) {
                // The best entry in mapModifiedTx has higher score
                // than the one from mapTx.
                // Switch which transaction (package) to consider
                iter = modit->iter;
                fUsingModified = true;
            } else {
                // Either no entry in mapModifiedTx, or it's worse than mapTx.
                // Increment mi for the next loop iteration.
                ++mi;
            }
        }

        // We skip mapTx entries that are inBlock, and mapModifiedTx shouldn't
        // contain anything that is inBlock.
        assert(!inBlock.count(iter));

        uint64_t packageSize = iter->GetSizeWithAncestors();
        CAmount packageFees = iter->GetModFeesWithAncestors();
        int64_t packageSigOpsCost = iter->GetSigOpCostWithAncestors();
        if (fUsingModified) {
            packageSize = modit->nSizeWithAncestors;
            packageFees = modit->nModFeesWithAncestors;
            packageSigOpsCost = modit->nSigOpCostWithAncestors;
        }

        if (packageFees < blockMinFeeRate.GetFee(packageSize)) {
            // Everything else we might consider has a lower fee rate
            return;
        }

        if (!TestPackage(packageSize, packageSigOpsCost)) {
            if (fUsingModified) {
                // Since we always look at the best entry in mapModifiedTx,
                // we must erase failed entries so that we can consider the
                // next best entry on the next loop iteration
                mapModifiedTx.get<ancestor_score>().erase(modit);
                failedTx.insert(iter);
            }

            ++nConsecutiveFailed;

            if (nConsecutiveFailed > MAX_CONSECUTIVE_FAILURES && nBlockWeight >
                    nBlockMaxWeight - 4000) {
                // Give up if we're close to full and haven't succeeded in a while
                break;
            }
            continue;
        }

        CTxMemPool::setEntries ancestors;
        uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
        std::string dummy;
        mempool.CalculateMemPoolAncestors(*iter, ancestors, nNoLimit, nNoLimit, nNoLimit, nNoLimit, dummy, false);

        onlyUnconfirmed(ancestors);
        ancestors.insert(iter);

        // Test if all tx's are Final
        if (!TestPackageTransactions(ancestors)) {
            if (fUsingModified) {
                mapModifiedTx.get<ancestor_score>().erase(modit);
                failedTx.insert(iter);
            }
            continue;
        }

        // This transaction will make it in; reset the failed counter.
        nConsecutiveFailed = 0;

        // Package can be added. Sort the entries in a valid order.
        std::vector<CTxMemPool::txiter> sortedEntries;
        SortForBlock(ancestors, sortedEntries);

        for (size_t i=0; i<sortedEntries.size(); ++i) {
            AddToBlock(sortedEntries[i]);
            // Erase from the modified set, if present
            mapModifiedTx.erase(sortedEntries[i]);
        }

        ++nPackagesSelected;

        // Update transactions that depend on each of these
        nDescendantsUpdated += UpdatePackagesForAdded(ancestors, mapModifiedTx);
    }
}
#endif

bool BlockAssembler::isStillDependent(CTxMemPool::txiter iter)
{
    for (CTxMemPool::txiter parent : mempool.GetMemPoolParents(iter))
    {
        if (!inBlock.count(parent)) {
            return true;
        }
    }
    return false;
}

void BlockAssembler::addTxs()
{
    std::stack<CTxMemPool::txiter> stack;
    std::set<CTxMemPool::txiter, CTxMemPool::CompareIteratorByHash> waitSet;
    typedef std::set<CTxMemPool::txiter, CTxMemPool::CompareIteratorByHash>::iterator waitIter;

    // fill stack with elements that are sorted by time with descending order.
    // note: to convert reverse iterator to forward iterator we use base()
    // but we need to add +1 to get iterator for the same element
    // operator+ is not supported for reverse iterators in boost
    // that is why we use ++ operator instead
    for (auto mi = mempool.mapTx.get<2>().rbegin(); mi != mempool.mapTx.get<2>().rend();)
        stack.push(mempool.mapTx.project<0>((++mi).base()));

    CTxMemPool::txiter iter;
    while (!stack.empty()) {
        iter = stack.top();
        stack.pop();

        // If tx already in block, skip
        if (inBlock.count(iter)) {
            assert(false); // shouldn't happen
            continue;
        }

        // If tx is dependent on other mempool txs which haven't yet been included
        // then put it in the waitSet
        if (isStillDependent(iter)) {
            waitSet.insert(iter);
            continue;
        }

        // ppcoin: timestamp limit
        if (iter->GetTx().nTime > GetAdjustedTime() || (pblock->IsProofOfStake() && iter->GetTx().nTime > pblock->vtx[1]->nTime))
            continue;

        if(!AddToBlock(iter))
            break; // Block is full

        // This tx was successfully added, so
        // add transactions that depend on this one to the stack to try again
        for (CTxMemPool::txiter child : mempool.GetMemPoolChildren(iter))
        {
            waitIter witer = waitSet.find(child);
            if (witer != waitSet.end()) {
                stack.push(child);
                waitSet.erase(witer);
            }
        }
    } //  while (!stack.empty())
} // BlockAssembler::addTxs()

void IncrementExtraNonce(CBlock* pblock, const CBlockIndex* pindexPrev, unsigned int& nExtraNonce)
{
    // Update nExtraNonce
    static uint256 hashPrevBlock;
    if (hashPrevBlock != pblock->hashPrevBlock)
    {
        nExtraNonce = 0;
        hashPrevBlock = pblock->hashPrevBlock;
    }
    ++nExtraNonce;
    unsigned int nHeight = pindexPrev->nHeight+1; // Height first in coinbase required for block.version=2
    CMutableTransaction txCoinbase(*pblock->vtx[0]);
    txCoinbase.vin[0].scriptSig = (CScript() << nHeight << CScriptNum(nExtraNonce)) + COINBASE_FLAGS;
    assert(txCoinbase.vin[0].scriptSig.size() <= 100);

    pblock->vtx[0] = MakeTransactionRef(std::move(txCoinbase));
    pblock->hashMerkleRoot = BlockMerkleRoot(*pblock);
    pblock->hashMyself.SetNull(); // Changed header, need reset cache!
}

static bool ProcessBlockFound(const CBlock* pblock, const CChainParams& chainparams)
{
    LogPrintf("%s\n", pblock->ToString());
    LogPrintf("generated %s\n", FormatMoney(pblock->vtx[0]->vout[0].nValue));

    // Found a solution
    {
        LOCK(cs_main);
        if (pblock->hashPrevBlock != ::ChainActive().Tip()->GetBlockHash())
            return error("EmercoinMiner: generated block is stale");
    }

    // Process this block the same as if we had received it from another node
    std::shared_ptr<const CBlock> shared_pblock = std::make_shared<const CBlock>(*pblock);
    if (!ProcessNewBlock(Params(), shared_pblock, true, NULL))
        return error("ProcessNewBlock, block not accepted");

    return true;
}

#ifdef ENABLE_WALLET
// We using following Minter thread to request external IP by STUN ~hourly
// It is needed, because of IP can be changed with VPNs, etc.
void ThreadGetMyExternalIP_STUN();

// Set within WalletFrame::currentWalletView()
// To get pointer to last selected wallet,
// or NULL, in case of emercoind
CWallet *g_LastWalletView = NULL;

static std::shared_ptr<CWallet> getCurrentWallet() {
    std::vector<std::shared_ptr<CWallet>> wallets = GetWallets();
    if(wallets.empty())
        return NULL;
    if(g_LastWalletView != 0)
        for(auto w : wallets)
            if(w.get() == g_LastWalletView)
                return w;
    return wallets[0];
}

void PoSMiner(std::shared_ptr<CWallet> pwallet)
{
    LogPrintf("CPUMiner started for proof-of-stake\n");
    util::ThreadRename("emercoin-stake-minter");

    unsigned int nExtraNonce = 0;

    CScript no_dest_script; // Dummy script for COINBASE TX in minted block
    // Do not compute timeout for pos as sqrt(numUTXO) anymore,
    // since several wallets, and contain changes
    unsigned int pos_timio = gArgs.GetArg("-staketimio", 1000);
    int64_t stun_timio_us = gArgs.GetArg("-stuntimio", 900) * 1000000;
    int64_t stun_next_request = stun_timio_us > 0? GetTimeMicros() + stun_timio_us : INT64_MAX;

    std::string strMintMessage = "Info: Minting suspended due to locked wallet.";

    const CWallet *pwallet_prev = pwallet.get();
    uint32_t    prev_nCommitCnt = pwallet_prev->m_nCommitCnt;
    try {
        while (true) {
            bool fInitialDownload = ::ChainstateActive().IsInitialBlockDownload();
            int64_t now = GetTimeMicros();
            if(now > stun_next_request) {
                ThreadGetMyExternalIP_STUN();
                // Seqientially add ~1% to stun_timio_us, for slowly increase STUN request intervals
                stun_timio_us += stun_timio_us / 128 + GetRandInt(1024 * 1024); // + ~0.5s randomization
                stun_next_request = now + stun_timio_us;
            }
            rc4ok_addentropy(bswap_16(now)); // For value other than in the Logger
            pwallet = getCurrentWallet();
            if(pwallet == NULL) {
                MilliSleep(300);
                continue;
            }
            if(pwallet.get() != pwallet_prev) {
                if(prev_nCommitCnt == pwallet->m_nCommitCnt)
                    pwallet->m_nCommitCnt++; // Force to drop PoS cache
                pwallet_prev = pwallet.get();
                prev_nCommitCnt = pwallet->m_nCommitCnt;
            }
            if(pwallet->IsLocked()) {
                if (strMintWarning != strMintMessage) {
                    strMintWarning = strMintMessage;
                    uiInterface.NotifyAlertChanged(uint256(), CT_UPDATED);
                }
                MilliSleep(3000);
                continue;
            }
            if(strMintWarning[0] != 0) {
                strMintWarning = "";  // clear locked wallet warning
                uiInterface.NotifyAlertChanged(uint256(), CT_UPDATED);
            }

            // Busy-wait for the network to come online so we don't waste time mining
            // on an obsolete chain. In regtest mode we expect to fly solo.
            if(g_connman == nullptr || g_connman->GetNodeCount(CConnman::CONNECTIONS_ALL) == 0 || fInitialDownload) {
                MilliSleep(5 * 1000); // wait for 5s (was 1 min)
                continue;
            }

            //
            // Create new block
            //
            CBlockIndex* pindexPrev = ::ChainActive().Tip();

            bool fPoSCancel = false;
            // For PoS, do not used new destination address for COINBASE
            // because of COINSTAKE uses and pays to already exists, matured address in the wallet
            std::unique_ptr<CBlockTemplate> pblocktemplate(BlockAssembler(Params()).CreateNewBlock(no_dest_script, pwallet.get(), &fPoSCancel));
            if (!pblocktemplate.get())
            {
                if (fPoSCancel == true)
                {
                    MilliSleep(pos_timio);
                    continue;
                }
                LogPrintf("Error in EmercoinMiner: Keypool ran out, please call keypoolrefill before restarting the mining thread\n");
                return;
            }
            CBlock *pblock = &pblocktemplate->block;
            IncrementExtraNonce(pblock, pindexPrev, nExtraNonce);

            // ppcoin: if proof-of-stake block found then process block
            if (pblock->IsProofOfStake())
            {
                {
                    LOCK2(cs_main, pwallet->cs_wallet);
                    if (!SignBlock(*pblock, *pwallet))
                    {
                        LogPrintf("PoSMiner(): failed to sign PoS block\n");
                        continue;
                    }
                }
                LogPrintf("CPUMiner : proof-of-stake block found %s\n", pblock->GetHash().ToString());
                ProcessBlockFound(pblock, Params());
                // Rest for ~3 minutes after successful block to preserve close quick
                MilliSleep(60 * 1000 + GetRandInt(4 * 60 * 1000));
            }
            MilliSleep(pos_timio);

            continue;
        } // while
    } // try
    catch (boost::thread_interrupted)
    {
        LogPrintf("EmercoinMiner terminated\n");
        return;
        // throw;
    }
    catch (const std::runtime_error &e)
    {
        LogPrintf("EmercoinMiner runtime error: %s\n", e.what());
        return;
    }
}

// ppcoin: stake minter thread
void ThreadStakeMinter(std::shared_ptr<CWallet> pwallet)
{
    LogPrintf("ThreadStakeMinter started\n");
    try
    {
        PoSMiner(pwallet);
    }
    catch (std::exception& e) {
        PrintExceptionContinue(&e, "ThreadStakeMinter()");
    } catch (...) {
        PrintExceptionContinue(NULL, "ThreadStakeMinter()");
    }
    LogPrintf("ThreadStakeMinter exiting\n");
}
#endif // ENABLE_WALLET


#if POW_MINING
//////////////////////////////////////////////////////////////////////////////
//
// Internal miner
//

//
// ScanHash scans nonces looking for a hash with at least some zero bits.
// The nonce is usually preserved between calls, but periodically or if the
// nonce is 0xffff0000 or above, the block is rebuilt and nNonce starts over at
// zero.
//
bool static ScanHash(const CBlockHeader *pblock, uint32_t& nNonce, uint256 *phash)
{
    // Write the first 76 bytes of the block header to a double-SHA256 state.
    CHash256 hasher;
    CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
    ss << *pblock;
    assert(ss.size() == 80);
    hasher.Write((unsigned char*)&ss[0], 76);

    while (true) {
        nNonce++;

        // Write the last 4 bytes of the block header (the nonce) to a copy of
        // the double-SHA256 state, and compute the result.
        CHash256(hasher).Write((unsigned char*)&nNonce, 4).Finalize((unsigned char*)phash);

        // Return the nonce if the hash has at least some zero bits,
        // caller will check if it has enough to reach the target
        if (((uint16_t*)phash)[15] == 0)
            return true;

        // If nothing found after trying for a while, return -1
        if ((nNonce & 0xfff) == 0)
            return false;
    }
}

// Helper function from src/rpc/mining.cpp
CScript BuildCoinbaseScript(const CTxDestination& dest, CWallet* const pwallet);

void static EmercoinMiner(const CChainParams& chainparams)
{
    LogPrintf("EmercoinMiner started\n");
    util::ThreadRename("emercoin-miner");

    unsigned int nExtraNonce = 0;

    std::shared_ptr<CWallet> pwallet = GetWallets()[0];
    if(pwallet == NULL)
        throw std::runtime_error("No coinbase script available (mining requires a wallet)");

    // For coinbase, we always must use P2PK (pay to pubkey) output script, since pubkey is needes
    // for generate block signature.
    ReserveDestination reservedest(pwallet.get());
    CTxDestination dest;
    if (!reservedest.GetReservedDestination(OutputType::LEGACY, dest, true))
        throw std::runtime_error("Error: Keypool ran out, please call keypoolrefill first");

    // Explicitly generate P2PK script for coinbase TX
    CScript scriptPubKeyCoinbase(BuildCoinbaseScript(dest, pwallet.get()));

    try {
        // Throw an error if no script was provided.  This can happen
        // due to some internal error but also if the keypool is empty.
        // In the latter case, already the pointer is NULL.
        //? if (!coinbaseScript || coinbaseScript->reserveScript.empty())
        //?     throw std::runtime_error("No coinbase script available (mining requires a wallet)");

        while (true) {
            // Busy-wait for the network to come online so we don't waste time mining
            // on an obsolete chain. In regtest mode we expect to fly solo.
            while(g_connman == nullptr || g_connman->GetNodeCount(CConnman::CONNECTIONS_ALL) == 0 || ::ChainstateActive().IsInitialBlockDownload())
                MilliSleep(1000);

            //
            // Create new block
            //
            unsigned int nTransactionsUpdatedLast = mempool.GetTransactionsUpdated();
            CBlockIndex* pindexPrev = ::ChainActive().Tip();

            std::unique_ptr<CBlockTemplate> pblocktemplate(BlockAssembler(Params()).CreateNewBlock(scriptPubKeyCoinbase, nullptr, nullptr));
            if (!pblocktemplate.get())
            {
                LogPrintf("Error in EmercoinMiner: Keypool ran out, please call keypoolrefill before restarting the mining thread\n"); // Exit here
                return;
            }
            CBlock *pblock = &pblocktemplate->block;
            IncrementExtraNonce(pblock, pindexPrev, nExtraNonce);

            LogPrintf("Running EmercoinMiner with %u transactions in block (%u bytes)\n", pblock->vtx.size(),
                ::GetSerializeSize(*pblock, SER_NETWORK, PROTOCOL_VERSION));

            //
            // Search
            //
            int64_t nStart = GetTime();
            arith_uint256 hashTarget = arith_uint256().SetCompact(pblock->nBits);
            uint256 hash;
            uint32_t nNonce = 0;
            while (true) {
                // Check if something found
                if (ScanHash(pblock, nNonce, &hash))
                {
                    if (UintToArith256(hash) <= hashTarget)
                    {
                        // Found a solution
                        pblock->nNonce = nNonce;
                        assert(hash == pblock->GetHash());
                        {
                            LOCK2(cs_main, pwallet->cs_wallet);
                            if (!SignBlock(*pblock, *pwallet))
                            {
                                LogPrintf("PoWMiner(): failed to sign PoW block\n");
                                continue;
                            }
                        }
                        LogPrintf("EmercoinMiner:\n");
                        LogPrintf("proof-of-work found  \n  hash: %s  \ntarget: %s\n", hash.GetHex(), hashTarget.GetHex());
                        ProcessBlockFound(pblock, chainparams);
                        reservedest.KeepDestination();

                        // In regression test mode, stop mining after a block is found.
                        if (chainparams.NetworkIDString() == "regtest")
                            throw boost::thread_interrupted();

                        break;
                    }
                }

                // Check for stop or if block needs to be rebuilt
                boost::this_thread::interruption_point();
                // Regtest mode doesn't require peers
                if ((g_connman == nullptr || g_connman->GetNodeCount(CConnman::CONNECTIONS_ALL) == 0))
                    break;
                if (nNonce >= 0xffff0000)
                    break;
                if (mempool.GetTransactionsUpdated() != nTransactionsUpdatedLast && GetTime() - nStart > 60)
                    break;
                if (pindexPrev != ::ChainActive().Tip())
                    break;

                // Update nTime every few seconds
                if (UpdateTime(pblock, chainparams.GetConsensus(), pindexPrev) < 0)
                    break; // Recreate the block if the clock has run backwards,
                           // so that we can use the correct time.
                if (chainparams.GetConsensus().fPowAllowMinDifficultyBlocks)
                {
                    // Changing pblock->nTime can change work required on testnet:
                    hashTarget.SetCompact(pblock->nBits);
                }
            } // while(true) 822
        } // while(true) 789
    }
    catch (const boost::thread_interrupted&)
    {
        LogPrintf("EmercoinMiner terminated\n");
        throw;
    }
    catch (const std::runtime_error &e)
    {
        LogPrintf("EmercoinMiner runtime error: %s\n", e.what());
        return;
    }
}

#include <boost/thread.hpp>

void GenerateEmercoins(bool fGenerate, int nThreads, const CChainParams& chainparams)
{
    static boost::thread_group* minerThreads = NULL;

    if (nThreads < 0)
        nThreads = GetNumCores();

    if (minerThreads != NULL)
    {
        minerThreads->interrupt_all();
        delete minerThreads;
        minerThreads = NULL;
    }

    if (nThreads == 0 || !fGenerate)
        return;

    minerThreads = new boost::thread_group();
    for (int i = 0; i < nThreads; i++)
        minerThreads->create_thread(boost::bind(&EmercoinMiner, boost::cref(chainparams)));
}
#endif
