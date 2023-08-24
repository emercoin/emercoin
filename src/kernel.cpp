// Copyright (c) 2012-2013 The PPCoin developers
// Distributed under the GPL3 software license, see the accompanying
// file COPYING or http://www.gnu.org/licenses/gpl.html.

#include <kernel.h>
#include <chainparams.h>
#include <validation.h>
#include <streams.h>
#include <uint256hm.h>
#include <wallet/wallet.h>
#include <timedata.h>
#include <consensus/validation.h>
#include <txdb.h>
#include <index/txindex.h>
#include <wallet/coincontrol.h>

using namespace std;
#if 0
// Hard checkpoints of stake modifiers to ensure they are deterministic
static std::map<int, unsigned int> mapStakeModifierCheckpoints =
{
    { 0,     0x0e00670bu },
    { 19000, 0xb185c126u }
};
#endif

// Get the last stake modifier and its generation time from a given block
static bool GetLastStakeModifier(const CBlockIndex* pindex, uint64_t& nStakeModifier, int64_t& nModifierTime)
{
    if (!pindex)
        return error("%s: null pindex", __func__);
    do {
        if (pindex->GeneratedStakeModifier()) {
            nStakeModifier = pindex->nStakeModifier;
            nModifierTime = pindex->GetBlockTime();
            return true;
        }
    } while ((pindex = pindex->pprev) != NULL);
    return error("%s: no generation at genesis block", __func__);
}

// Get selection interval section (in seconds)
static int64_t GetStakeModifierSelectionIntervalSection(int nSection)
{
    assert (nSection >= 0 && nSection < 64);
    return (Params().GetConsensus().nStakeModifierInterval * 63 / (63 + ((63 - nSection) * (MODIFIER_INTERVAL_RATIO - 1))));
}

// Get stake modifier selection interval (in seconds)
static int64_t GetStakeModifierSelectionInterval()
{
    static int64_t nSelectionInterval = -1;
    if (nSelectionInterval < 0) {
        nSelectionInterval = 0;
        for (int nSection=0; nSection<64; nSection++)
            nSelectionInterval += GetStakeModifierSelectionIntervalSection(nSection);
    }
    return nSelectionInterval;
}

// select a block from the candidate blocks in vSortedByTimestamp, excluding
// already selected blocks in vSelectedBlocks, and with timestamp up to
// nSelectionIntervalStop.
static bool SelectBlockFromCandidates(
    vector<pair<const CBlockIndex*, arith_uint256> >& vSortedByTimestamp,
    int64_t nSelectionIntervalStop, uint64_t nStakeModifierPrev,
    const CBlockIndex** pindexSelected)
{
    arith_uint256 zero = 0;
    pair<const CBlockIndex*, arith_uint256> *itemSelected = NULL;

    for (auto& item : vSortedByTimestamp) {
        const CBlockIndex* pindex = item.first;
        if (pindex == NULL)
            continue; // This block already has been selected

        if (itemSelected != NULL && pindex->GetBlockTime() > nSelectionIntervalStop)
            break;

        if (itemSelected == NULL || item.second < itemSelected->second) {
            // compute the selection hash by hashing its proof-hash and the
            // previous proof-of-stake modifier
            if (item.second == zero) {
                uint256 hashProof = pindex->IsProofOfStake()? pindex->hashProofOfStake : pindex->GetBlockHash();
                CDataStream ss(SER_GETHASH, 0);
                ss << hashProof << nStakeModifierPrev;
                item.second = UintToArith256(Hash(ss.begin(), ss.end()));
                // the selection hash is divided by 2**32 so that proof-of-stake block
                // is always favored over proof-of-work block. this is to preserve
                // the energy efficiency property
                if (pindex->IsProofOfStake())
                    item.second >>= 32;

                if (itemSelected != NULL && item.second >= itemSelected->second)
                    continue;
            }
            itemSelected = &item;
        }
    } // for

    if (itemSelected) {
        if (gArgs.GetBoolArg("-printstakemodifier", false))
            LogPrintf("%s: selection hash=%s\n", __func__, itemSelected->second.ToString());
        *pindexSelected = itemSelected->first;
        itemSelected->first = NULL;
        return true;
    } else {
        *pindexSelected = (const CBlockIndex*) 0;
        return false;
    }
}

static void SwapSort(vector<pair<const CBlockIndex*, arith_uint256> > &v, unsigned pos) {
  if(pos >= v.size() - 1)
	  return;

  pair<const CBlockIndex*, arith_uint256> &a = v[pos];
  pair<const CBlockIndex*, arith_uint256> &b = v[pos + 1];

  if (a.first->GetBlockTime() < b.first->GetBlockTime())
    return;

  if (a.first->GetBlockTime() == b.first->GetBlockTime()) {

    const uint256& ha = a.first->GetBlockHash(); // needed because of weird g++ (5.4.0 20160609) bug
    const uint256& hb = b.first->GetBlockHash();
    const uint32_t *pa = ha.GetDataPtr();
    const uint32_t *pb = hb.GetDataPtr();
    int cnt = 256 / 32;
    for( ; ; ) {
      --cnt;
      if(pa[cnt] < pb[cnt])
	return;
      if(pa[cnt] > pb[cnt])
        break; // go to swap
      if(cnt == 0)
	return;
    }
  }

  std::swap(a, b);
  SwapSort(v, pos - 1);
  SwapSort(v, pos + 1);
} // SwapSort


// Stake Modifier (hash modifier of proof-of-stake):
// The purpose of stake modifier is to prevent a txout (coin) owner from
// computing future proof-of-stake generated by this txout at the time
// of transaction confirmation. To meet kernel protocol, the txout
// must hash with a future stake modifier to generate the proof.
// Stake modifier consists of bits each of which is contributed from a
// selected block of a given block group in the past.
// The selection of a block is based on a hash of the block's proof-hash and
// the previous stake modifier.
// Stake modifier is recomputed at a fixed time interval instead of every
// block. This is to make it difficult for an attacker to gain control of
// additional bits in the stake modifier, even after generating a chain of
// blocks.
bool ComputeNextStakeModifier(const CBlockIndex* pindexCurrent, uint64_t& nStakeModifier, bool& fGeneratedStakeModifier)
{
    const CBlockIndex* pindexPrev = pindexCurrent->pprev;
    nStakeModifier = 0;
    fGeneratedStakeModifier = false;
    if (!pindexPrev)
    {
        fGeneratedStakeModifier = true;
        return true;  // genesis block's modifier is 0
    }
    // First find current stake modifier and its generation block time
    // if it's not old enough, return the same stake modifier
    int64_t nModifierTime = 0;
    if (!GetLastStakeModifier(pindexPrev, nStakeModifier, nModifierTime))
        return error("%s: unable to get last modifier", __func__);
    static int fPrint =-1;
    if (fPrint < 0)
        fPrint = gArgs.GetBoolArg("-printstakemodifier", false);
    if (fPrint)
        LogPrintf("%s: prev modifier=0x%016x time=%s epoch=%u\n", __func__, nStakeModifier, FormatISO8601DateTime(nModifierTime), (unsigned int)nModifierTime);
    const Consensus::Params& params = Params().GetConsensus();
    if (nModifierTime / params.nStakeModifierInterval >= pindexPrev->GetBlockTime() / params.nStakeModifierInterval)
    // if (nModifierTime + params.nStakeModifierInterval > pindexPrev->GetBlockTime())
    {
        if (fPrint)
            LogPrintf("%s: no new interval keep current modifier: pindexPrev nHeight=%d nTime=%u\n", __func__, pindexPrev->nHeight, (unsigned int)pindexPrev->GetBlockTime());
        return true;
    }
    if (nModifierTime / params.nStakeModifierInterval >= pindexCurrent->GetBlockTime() / params.nStakeModifierInterval)
    // if (nModifierTime + params.nStakeModifierInterval > pindexCurrent->GetBlockTime())
    {
        // v0.4+ requires current block timestamp also be in a different modifier interval
        if (IsProtocolV04(pindexCurrent->nTime))
        {
            if (fPrint)
                LogPrintf("%s: (v0.3.5+) no new interval keep current modifier: pindexCurrent nHeight=%d nTime=%u\n", __func__, pindexCurrent->nHeight, (unsigned int)pindexCurrent->GetBlockTime());
            return true;
        }
        else if (fPrint)
                LogPrintf("%s: v0.3.4 modifier at block %s not meeting v0.4+ protocol: pindexCurrent nHeight=%d nTime=%u\n", __func__, pindexCurrent->GetBlockHash().ToString(), pindexCurrent->nHeight, (unsigned int)pindexCurrent->GetBlockTime());
    }

    // Sort candidate blocks by timestamp
    vector<pair<const CBlockIndex*, arith_uint256> > vSortedByTimestamp;
    vSortedByTimestamp.reserve(64 * params.nStakeModifierInterval / params.nStakeTargetSpacing + 1);
    int64_t nSelectionInterval = GetStakeModifierSelectionInterval();
    int64_t nSelectionIntervalStart = (pindexPrev->GetBlockTime() / params.nStakeModifierInterval) * params.nStakeModifierInterval - nSelectionInterval;
    const CBlockIndex* pindex = pindexPrev;
    while (pindex && pindex->GetBlockTime() >= nSelectionIntervalStart) {
        if (!LookupBlockIndex(pindex->GetBlockHash()))
            return error("%s: failed to find block index for candidate block %s", __func__, pindex->GetBlockHash().ToString());
        vSortedByTimestamp.push_back(make_pair(pindex, 0));
        pindex = pindex->pprev;
    }

    reverse(vSortedByTimestamp.begin(), vSortedByTimestamp.end());
    for(int i = 0; i < (int)vSortedByTimestamp.size() - 1; i++)
	    SwapSort(vSortedByTimestamp, i);

    // Select 64 blocks from candidate blocks to generate stake modifier
    uint64_t nStakeModifierNew = 0;
    int64_t nSelectionIntervalStop = nSelectionIntervalStart;
    for (int nRound=0; nRound<min(64, (int)vSortedByTimestamp.size()); nRound++)
    {
        // add an interval section to the current selection round
        nSelectionIntervalStop += GetStakeModifierSelectionIntervalSection(nRound);
        // select a block from the candidates of current round
        if (!SelectBlockFromCandidates(vSortedByTimestamp, nSelectionIntervalStop, nStakeModifier, &pindex))
            return error("%s: unable to select block at round %d", __func__, nRound);
        // write the entropy bit of the selected block
        nStakeModifierNew |= (((uint64_t)pindex->GetStakeEntropyBit()) << nRound);
        // add the selected block from candidates to selected list
        if (gArgs.GetBoolArg("-printstakemodifier", false))
            LogPrintf("%s: selected round %d stop=%s height=%d bit=%d\n", __func__,
                nRound, FormatISO8601DateTime(nSelectionIntervalStop), pindex->nHeight, pindex->GetStakeEntropyBit());
    }

    if (fPrint)
        LogPrintf("%s: new modifier=0x%016x time=%s\n", __func__, nStakeModifierNew, FormatISO8601DateTime(pindexPrev->GetBlockTime()));

    nStakeModifier = nStakeModifierNew;
    fGeneratedStakeModifier = true;
    return true;
}

// V0.5: Stake modifier used to hash for a stake kernel is chosen as the stake
// modifier that is (nStakeMinAge minus a selection interval) earlier than the
// stake, thus at least a selection interval later than the coin generating the // kernel, as the generating coin is from at least nStakeMinAge ago.
static bool GetKernelStakeModifierV05(CBlockIndex* pindexPrev, unsigned int nTimeTx, uint64_t& nStakeModifier, int& nStakeModifierHeight, int64_t& nStakeModifierTime)
{
    const Consensus::Params& params = Params().GetConsensus();
    const CBlockIndex* pindex = pindexPrev;
    nStakeModifierHeight = pindex->nHeight;
    nStakeModifierTime = pindex->GetBlockTime();
    int64_t nStakeModifierSelectionInterval = GetStakeModifierSelectionInterval();

    if (nStakeModifierTime + params.nStakeMinAge - nStakeModifierSelectionInterval <= (int64_t) nTimeTx)
    {
        // Best block is still more than
        // (nStakeMinAge minus a selection interval) older than kernel timestamp
        //return error("GetKernelStakeModifier() : best block %s at height %d too old for stake", pindex->GetBlockHash().ToString(), pindex->nHeight);
        return false;
    }

    static int64_t       cache_TimeTxBarrier = 0;
    static int64_t       cache_nStakeModifierTime, cache_nStakeModifierTime_in;
    static uint64_t      cache_nStakeModifier;
    static int           cache_nStakeModifierHeight;
    static unsigned int  cache_nTimeTx;
    static int           modcache = -1; // 0=disable; 1=InitialDownload; 2=always
    if(modcache < 0)
        modcache = gArgs.GetArg("-modcache", 1);
    if (modcache > 1 || (modcache > 0 && ::ChainstateActive().IsInitialBlockDownload())) {
        if(nTimeTx <= cache_TimeTxBarrier && nStakeModifierTime >= cache_nStakeModifierTime_in && nTimeTx >= cache_nTimeTx) {
            nStakeModifier       = cache_nStakeModifier;
            nStakeModifierTime   = cache_nStakeModifierTime;
            nStakeModifierHeight = cache_nStakeModifierHeight;
            return true;
        }
        cache_nStakeModifierTime_in = nStakeModifierTime;
    } // modcache
    // loop to find the stake modifier earlier by
    // (nStakeMinAge minus a selection interval)
    while (nStakeModifierTime + params.nStakeMinAge - nStakeModifierSelectionInterval >(int64_t) nTimeTx)
    {
        if (!pindex->pprev)
        {   // reached genesis block; should not happen
            return error("GetKernelStakeModifier() : reached genesis block");
        }
        pindex = pindex->pprev;
        if (pindex->GeneratedStakeModifier())
        {
            nStakeModifierHeight = pindex->nHeight;
            nStakeModifierTime = pindex->GetBlockTime();
            cache_TimeTxBarrier = nStakeModifierTime + params.nStakeMinAge - nStakeModifierSelectionInterval;
        }
    } // while
    cache_nStakeModifier = nStakeModifier = pindex->nStakeModifier;
    cache_nStakeModifierHeight = nStakeModifierHeight;
    cache_nStakeModifierTime = nStakeModifierTime;
    cache_nTimeTx = nTimeTx;
    return true;
}

// The stake modifier used to hash for a stake kernel is chosen as the stake
// modifier about a selection interval later than the coin generating the kernel
static bool GetKernelStakeModifierV03(CBlockIndex* pindexPrev, uint256 hashBlockFrom, uint64_t& nStakeModifier, int& nStakeModifierHeight, int64_t& nStakeModifierTime)
{
    const Consensus::Params& params = Params().GetConsensus();
    nStakeModifier = 0;
    const CBlockIndex* pindexFrom = LookupBlockIndex(hashBlockFrom);
    if (!pindexFrom)
        return error("%s: block not indexed", __func__);
    nStakeModifierHeight = pindexFrom->nHeight;
    nStakeModifierTime = pindexFrom->GetBlockTime();
    int64_t nStakeModifierSelectionInterval = GetStakeModifierSelectionInterval();

    // emercoin: we need to iterate index forward but we cannot use ::ChainActive().Next()
    // because there is no guarantee that we are checking blocks in active chain.
    // So, we construct a temporary chain that we will iterate over.
    // pindexFrom - this block contains coins that are used to generate PoS
    // pindexPrev - this is a block that is previous to PoS block that we are checking, you can think of it as tip of our chain
    // tmpChain should contain all indexes in [pindexFrom..pindexPrev] (inclusive)
    std::vector<CBlockIndex*> tmpChain;
    int32_t nDepth = pindexPrev->nHeight - (pindexFrom->nHeight-1); // -1 is used to also include pindexFrom
    tmpChain.reserve(nDepth);
    CBlockIndex* it = pindexPrev;
    for (int i=1; i<=nDepth && !::ChainActive().Contains(it); i++) {
        tmpChain.push_back(it);
        it = it->pprev;
    }

    std::reverse(tmpChain.begin(), tmpChain.end());

    size_t n = 0;
    const CBlockIndex* pindex = pindexFrom;
    // loop to find the stake modifier later by a selection interval
    while (nStakeModifierTime < pindexFrom->GetBlockTime() + nStakeModifierSelectionInterval)
    {
        const CBlockIndex* old_pindex = pindex;
        pindex = (!tmpChain.empty() && pindex->nHeight >= tmpChain[0]->nHeight - 1)? tmpChain[n++] : ::ChainActive().Next(pindex);
        if (n > tmpChain.size() || pindex == NULL) // check if tmpChain[n+1] exists
        {   // reached best block; may happen if node is behind on block chain
            auto cat = old_pindex->GetBlockTime() + params.nStakeMinAge - nStakeModifierSelectionInterval > GetAdjustedTime() ? BCLog::NONE : BCLog::STAKE;
            LogPrint(cat, "%s: reached best block %s at height %d from block %s", __func__,
                     old_pindex->GetBlockHash().ToString(), old_pindex->nHeight, hashBlockFrom.ToString());
            return false;
        }
        if (pindex->GeneratedStakeModifier())
        {
            nStakeModifierHeight = pindex->nHeight;
            nStakeModifierTime = pindex->GetBlockTime();
        }
    }
    nStakeModifier = pindex->nStakeModifier;

    return true;
}

// Get the stake modifier specified by the protocol to hash for a stake kernel
static bool GetKernelStakeModifier(CBlockIndex* pindexPrev, uint256 hashBlockFrom, unsigned int nTimeTx, uint64_t& nStakeModifier, int& nStakeModifierHeight, int64_t& nStakeModifierTime)
{
    if (IsProtocolV05(nTimeTx))
        return GetKernelStakeModifierV05(pindexPrev, nTimeTx, nStakeModifier, nStakeModifierHeight, nStakeModifierTime);
    else
        return GetKernelStakeModifierV03(pindexPrev, hashBlockFrom, nStakeModifier, nStakeModifierHeight, nStakeModifierTime);
}

// ppcoin kernel protocol
// coinstake must meet hash target according to the protocol:
// kernel (input 0) must meet the formula
//     hash(nStakeModifier + txPrev.block.nTime + txPrev.offset + txPrev.nTime + txPrev.vout.n + nTime) < bnTarget * nCoinDayWeight
// this ensures that the chance of getting a coinstake is proportional to the
// amount of coin age one owns.
// The reason this hash is chosen is the following:
//   nStakeModifier:
//       (v0.5) uses dynamic stake modifier around 21 days before the kernel,
//              versus static stake modifier about 9 days after the staked
//              coin (txPrev) used in v0.3
//       (v0.3) scrambles computation to make it very difficult to precompute
//              future proof-of-stake at the time of the coin's confirmation
//       (v0.2) nBits (deprecated): encodes all past block timestamps
//   txPrev.block.nTime: prevent nodes from guessing a good timestamp to
//                       generate transaction for future advantage
//   txPrev.offset: offset of txPrev inside block, to reduce the chance of
//                  nodes generating coinstake at the same time
//   txPrev.nTime: reduce the chance of nodes generating coinstake at the same
//                 time
//   txPrev.vout.n: output number of txPrev, to reduce the chance of nodes
//                  generating coinstake at the same time
//   block/tx hash should not be used here as they can be generated in vast
//   quantities so as to generate blocks faster, degrading the system back into
//   a proof-of-work situation.
//
static bool CheckStakeKernelHash(unsigned int nBits, CBlockIndex* pindexPrev, const CBlockHeader& blockFrom, unsigned int nTxPrevOffset, const CTransactionRef& txPrev, const COutPoint& prevout, unsigned int nTimeTx, uint256& hashProofOfStake)
{
    const Consensus::Params& params = Params().GetConsensus();
    if (nTimeTx < txPrev->nTime)  // Transaction timestamp violation
        return error("%s: nTime violation", __func__);

    unsigned int nTimeBlockFrom = blockFrom.GetBlockTime();
    if (nTimeBlockFrom + params.nStakeMinAge > nTimeTx) // Min age requirement
        return error("%s: min age violation", __func__);

    arith_uint256 bnTargetPerCoinDay;
    bnTargetPerCoinDay.SetCompact(nBits);
    int64_t nValueIn = txPrev->vout[prevout.n].nValue;
    // v0.3 protocol kernel hash weight starts from 0 at the 30-day min age
    // this change increases active coins participating the hash and helps
    // to secure the network when proof-of-stake difficulty is low
    int64_t nTimeWeight = min((int64_t)nTimeTx - txPrev->nTime, params.nStakeMaxAge) - (IsProtocolV03(nTimeTx)? params.nStakeMinAge : 0);
    arith_uint256 bnCoinDayWeight = arith_uint256(nValueIn) * nTimeWeight / COIN / (24 * 60 * 60);
    // Calculate hash
    CDataStream ss(SER_GETHASH, 0);
    uint64_t nStakeModifier = 0;
    int nStakeModifierHeight = 0;
    int64_t nStakeModifierTime = 0;
    if (IsProtocolV03(nTimeTx)) {  // v0.3 protocol
        if (!GetKernelStakeModifier(pindexPrev, blockFrom.GetHash(), nTimeTx, nStakeModifier, nStakeModifierHeight, nStakeModifierTime))
            return false;
        ss << nStakeModifier;
    } else {                       // v0.2 protocol
        ss << nBits;
    }

    ss << nTimeBlockFrom << nTxPrevOffset << txPrev->nTime << prevout.n << nTimeTx;

    if (nTimeTx >= 1489782503 && !IsProtocolV05(nTimeTx)) // block 219831, until 06/18/2019
        ss << pindexPrev->GetBlockHash();

    hashProofOfStake = Hash(ss.begin(), ss.end());

    // Now check if proof-of-stake hash meets target protocol
    bool fPass = !(UintToArith256(hashProofOfStake) > bnCoinDayWeight * bnTargetPerCoinDay);
#if 0
    // This is debug code, deactivate here
    if (IsProtocolV03(nTimeTx))
        LogPrint(fPass ? BCLog::NONE : BCLog::STAKE, "%s: using modifier 0x%016x at height=%d timestamp=%s for block from height=%d timestamp=%s\n", __func__,
            nStakeModifier, nStakeModifierHeight,
            FormatISO8601DateTime(nStakeModifierTime),
            LookupBlockIndex(blockFrom.GetHash())->nHeight,
            FormatISO8601DateTime(blockFrom.GetBlockTime()));
    LogPrint(fPass ? BCLog::NONE : BCLog::STAKE, "%s: check protocol=%s modifier=0x%016x nTimeBlockFrom=%u nTxPrevOffset=%u nTimeTxPrev=%u nPrevout=%u nTimeTx=%u hashProof=%s\n", __func__,
        IsProtocolV05(nTimeTx)? "0.5" : (IsProtocolV03(nTimeTx)? "0.3" : "0.2"),
        IsProtocolV03(nTimeTx)? nStakeModifier : (uint64_t) nBits,
        nTimeBlockFrom, nTxPrevOffset, txPrev->nTime, prevout.n, nTimeTx,
        hashProofOfStake.ToString());
#endif
    return fPass;
}

// Check kernel hash target and coinstake signature
bool CheckProofOfStake(CValidationState &state, CBlockIndex* pindexPrev, const CTransactionRef& tx, unsigned int nBits, uint256& hashProofOfStake)
{
    if (!tx->IsCoinStake())
        return error("CheckProofOfStake() : called on non-coinstake %s", tx->GetHash().ToString());

    // Kernel (input 0) must match the stake hash target per coin age (nBits)
    const CTxIn& txin = tx->vin[0];

    // Transaction index is required to get to block header
    if (!g_txindex)
        return error("CheckProofOfStake() : transaction index not available");

    // Get transaction index for the previous transaction
    CDiskTxPos postx;
    if (!g_txindex->FindTxPosition(txin.prevout.hash, postx))
        return error("CheckProofOfStake() : tx index not found");  // tx index not found

    // Read txPrev and header of its block
    CBlockHeader header;
    CTransactionRef txPrev;
    {
        CAutoFile file(OpenBlockFile(postx, true), SER_DISK, CLIENT_VERSION);
        if (file.IsNull()) {
            return error("%s: OpenBlockFile failed", __func__);
        }
        try {
            file >> header;
            if (fseek(file.Get(), postx.nTxOffset, SEEK_CUR)) {
                return error("%s: fseek(...) failed", __func__);
            }
            file >> txPrev;
        } catch (std::exception &e) {
            return error("%s: Deserialize or I/O error - %s", __func__, e.what());
        }
        if (txPrev->GetHash() != txin.prevout.hash) {
            return error("%s: txid mismatch", __func__);
        }
    }

    // Verify signature
    {
        int nIn = 0;
        const CTxOut& prevOut = txPrev->vout[tx->vin[nIn].prevout.n];
        TransactionSignatureChecker checker(&(*tx), nIn, prevOut.nValue, PrecomputedTransactionData(*tx));

        if (!VerifyScript(tx->vin[nIn].scriptSig, prevOut.scriptPubKey, tx->nVersion, &(tx->vin[nIn].scriptWitness), SCRIPT_VERIFY_P2SH, checker, nullptr))
            return state.Invalid(ValidationInvalidReason::CONSENSUS, false, REJECT_INVALID, "invalid-pos-script", strprintf("%s: VerifyScript failed on coinstake %s", __func__, tx->GetHash().ToString()));
    }

    if (!CheckStakeKernelHash(nBits, pindexPrev, header, postx.nTxOffset + CBlockHeader::NORMAL_SERIALIZE_SIZE, txPrev, txin.prevout, tx->nTime, hashProofOfStake))
        return state.Invalid(ValidationInvalidReason::CONSENSUS, false, REJECT_INVALID, "invalid-stake-hash", strprintf("%s: INFO: check kernel failed on coinstake %s, hashProof=%s", __func__, tx->GetHash().ToString(), hashProofOfStake.ToString()));

    return true;
}

// Check whether the coinstake timestamp meets protocol
bool CheckCoinStakeTimestamp(int64_t nTimeBlock, int64_t nTimeTx)
{
    if (IsProtocolV03(nTimeTx))  // v0.3 protocol
        return (nTimeBlock == nTimeTx);
    else // v0.2 protocol
        return ((nTimeTx <= nTimeBlock) && (nTimeBlock <= nTimeTx + nMaxClockDrift));
}

// Get stake modifier checksum
unsigned int GetStakeModifierChecksum(const CBlockIndex* pindex)
{
    assert (pindex->pprev || pindex->GetBlockHash() == Params().GetConsensus().hashGenesisBlock);
    // Hash previous checksum with flags, hashProofOfStake and nStakeModifier
    CDataStream ss(SER_GETHASH, 0);
    if (pindex->pprev)
        ss << pindex->pprev->nStakeModifierChecksum;
    unsigned int nFlags = pindex->nFlags & ~HEADER_CHECKPOINT_VALIDATED;  // emc - remove HEADER_CHECKPOINT_VALIDATED flag from checksum
    ss << nFlags << pindex->hashProofOfStake << pindex->nStakeModifier;
    arith_uint256 hashChecksum = UintToArith256(Hash(ss.begin(), ss.end()));
    hashChecksum >>= (256 - 32);
    return hashChecksum.GetLow64();
}

// Check stake modifier hard checkpoints
bool CheckStakeModifierCheckpoints(int nHeight, unsigned int nStakeModifierChecksum)
{
#if 0
    if (Params().NetworkIDString() != "main") return true; // Testnet or Regtest has no checkpoints
    if (mapStakeModifierCheckpoints.count(nHeight))
        return nStakeModifierChecksum == mapStakeModifierCheckpoints[nHeight];
#endif
    return true;
}

// ppcoin: create coin stake transaction
typedef std::vector<unsigned char> valtype;
bool CreateCoinStake(const CWallet* pwallet, unsigned int nBits, int64_t nSearchInterval, CMutableTransaction& txNew)
{
    // Transaction index is required to get to block header
    if (!g_txindex)
        return error("CreateCoinStake : transaction index unavailable");

    const Consensus::Params& params = Params().GetConsensus();
    // The following split & combine thresholds are important to security
    // Should not be adjusted if you don't understand the consequences
    static unsigned int nStakeSplitAge = (60 * 60 * 24 * 90);
    LOCK2(cs_main, pwallet->cs_wallet);
    CAmount nPoWReward = GetProofOfWorkReward(GetLastBlockIndex(::ChainActive().Tip(), false)->nBits);
    // used within coinstake collector, disabled since 0.8.0     CAmount nCombineThreshold = nPoWReward / 3;

    arith_uint256 bnTargetPerCoinDay;
    bnTargetPerCoinDay.SetCompact(nBits);

    txNew.vin.clear();
    txNew.vout.clear();
    // Mark coin stake transaction
    CScript scriptEmpty;
    scriptEmpty.clear();
    txNew.vout.push_back(CTxOut(0, scriptEmpty));
    // Choose coins to use
    CAmount nBalance = pwallet->GetBalance().m_mine_trusted;
    CAmount nReserveBalance = 0;
    if (gArgs.IsArgSet("-reservebalance") && !ParseMoney(gArgs.GetArg("-reservebalance", ""), nReserveBalance))
        return error("CreateCoinStake : invalid reserve balance amount");
    if (nBalance <= nReserveBalance)
        return false;
    std::vector<CTransactionRef> vtxPrev;
    CAmount nValueIn = 0;
    static std::set<CInputCoin> setCoins;
    static uint32_t prev_committed_txes = ~0; // Undef, need reload setCoins
    if(pwallet->m_nCommitCnt != prev_committed_txes || GetRand(3 * 3600) == 0) {
        // Something changed in the wallet, reload setCoins
        // Also, randomly every ~3 hours to refresh possible unsynch UTXOs (i.e. sent from another wallet)
        setCoins.clear();
        std::vector<COutput> vAvailableCoins;
        bool include_unsafe = false;
        CCoinControl cctl;
        cctl.m_avoid_address_reuse = false;
        cctl.m_min_depth = 1;
        cctl.m_max_depth = 9999999;
        CAmount nMinimumAmount = 0;
        CAmount nMaximumAmount = MAX_MONEY;
        CAmount nMinimumSumAmount = MAX_MONEY;
        uint64_t nMaximumCount = 0;
        auto locked_chain = pwallet->chain().lock();
        LOCK(pwallet->cs_wallet);
        pwallet->AvailableCoins(*locked_chain, vAvailableCoins, include_unsafe, &cctl, nMinimumAmount, nMaximumAmount, nMinimumSumAmount, nMaximumCount);

        bool bnb_used;
        CoinSelectionParams coin_selection_params; // Parameters for coin selection, init with dummy
        if (!pwallet->SelectCoins(vAvailableCoins, nBalance - nReserveBalance, setCoins, nValueIn, cctl, coin_selection_params, bnb_used)) {
            return false;
        }
        prev_committed_txes = pwallet->m_nCommitCnt;
    }

    if (setCoins.empty())
        return false;
    CAmount nCredit = 0;
    CScript scriptPubKeyKernel;

    // This is static cache for minimize block loads for each POS-attempt
    // Possible values of ->value.first
    // Addr > 0x4 -- This is pointer to blockheader in the memory
    // Addr = 0x1 -- Was read error, don't load this block anymore
    // NULL -- Block removed after mint, but maybe need reload again into same cell
    static uint256HashMap<std::pair<CBlockHeader*, unsigned int> > CacheBlockOffset;
    CacheBlockOffset.Set(setCoins.size() << 1); // 2x pointers
    uint256HashMap<std::pair<CBlockHeader*, unsigned int> >::Data *pbo = NULL;

    int nSplitPos = gArgs.GetArg("-splitpos", 1); // 0=No Split, 1=RandSplit before 90d, -1=Principal+Reward

    for (const auto& pcoin : setCoins)
    {
        uint256 tx_hash = pcoin.outpoint.hash;
        pbo = CacheBlockOffset.Search(tx_hash);
        // Try Load, if missing or temporary removed
        if (pbo == NULL || pbo->value.first == NULL) {
          CDiskTxPos postx;
          CBlockHeader *cbh = (CBlockHeader *)0x1; // default=Error
          if (g_txindex && g_txindex->FindTxPosition(tx_hash, postx)) {
            // Read block header
            CAutoFile file(OpenBlockFile(postx, true), SER_DISK, CLIENT_VERSION);
            cbh = new CBlockHeader;
            try {
              file >> *cbh;
            } catch (std::exception &e) {
          delete cbh;
          cbh = (CBlockHeader *)0x1; // Error
            }
          } // ReadTxIndex()

          if (pbo == NULL) {
              std::pair<CBlockHeader*, unsigned int> bo(cbh, postx.nTxOffset + CBlockHeader::NORMAL_SERIALIZE_SIZE);
              pbo = CacheBlockOffset.Insert(tx_hash, bo);
          } else
              pbo->value.first = cbh;
        } // if(pbo == NULL)

        // Don't work, if reaadErr=0x1, or temporary removed=NULL
        if(pbo->value.first < (CBlock*)0x4)
            continue;

        CBlockHeader& header = *(pbo->value.first);
        unsigned int offset  = pbo->value.second;


        static int nMaxStakeSearchInterval = 60;
        if (header.GetBlockTime() + params.nStakeMinAge > txNew.nTime - nMaxStakeSearchInterval)
            continue; // only count coins meeting min age requirement

        uint256 hashBlock = uint256();
        CTransactionRef tx;
        if (!g_txindex->FindTx(tx_hash, hashBlock, tx))
            return error("failed to find tx");

        uint256 hashProofOfStake; // Dummy, write only
        bool fKernelFound = false;
        for (unsigned int n=0; n<std::min(nSearchInterval,(int64_t)nMaxStakeSearchInterval) && !fKernelFound; n++)
        {
            // Search backward in time from the given txNew timestamp
            // Search nSearchInterval seconds back up to nMaxStakeSearchInterval
            if (CheckStakeKernelHash(nBits, ::ChainActive().Tip(), header, offset, tx, pcoin.outpoint, txNew.nTime - n, hashProofOfStake))
            {
                // Found a kernel
                bool f_printcoinstake = gArgs.GetBoolArg("-printcoinstake", false);
                if (f_printcoinstake)
                    LogPrintf("CreateCoinStake : kernel found\n");
                std::vector<valtype> vSolutions;
                scriptPubKeyKernel = pcoin.txout.scriptPubKey;
                txnouttype whichType = Solver(scriptPubKeyKernel, vSolutions);
                CScript scriptPubKeyOut;
                if (f_printcoinstake)
                    LogPrintf("CreateCoinStake : parsed kernel type=%s\n", GetTxnOutputType(whichType));

                // On ScriptHash - unpack external P2SH layer, to extract script for future processing
                if (whichType == TX_WITNESS_V0_SCRIPTHASH || whichType == TX_SCRIPTHASH) {
                    uint160 hash;
                    if(whichType == TX_SCRIPTHASH)
                        hash = uint160(vSolutions[0]);
                    else
                        CRIPEMD160().Write(&vSolutions[0][0], vSolutions[0].size()).Finalize(hash.begin());
                     CScriptID scriptID(hash);
                     // Unpack p2sh and rewrite scriptPubKeyKernel
                     if (!pwallet->GetCScript(scriptID, scriptPubKeyKernel)) {
                        if (f_printcoinstake)
                            LogPrintf("CreateCoinStake : failed unpack P2SH/P2WSH script for type=%s\n", GetTxnOutputType(whichType));
                        break;  // unable to find corresponding nested p2sh script
                     }
                     // Re-solve nested P2SH/P2WSH script again
                     whichType = Solver(scriptPubKeyKernel, vSolutions);
                        if (f_printcoinstake)
                            LogPrintf("CreateCoinStake : unpacked P2SH/P2WSH to type=%s\n", GetTxnOutputType(whichType));
                } // P2SH/P2WSH

                if (whichType == TX_PUBKEYHASH          || // was before
                    whichType == TX_WITNESS_V0_KEYHASH     // OK on testnet
                  ) { // pay to address type
                    // convert to pay to public key type
                    // we need natural key for sign/verify PoS block
                    CKey key;
                    if (!pwallet->GetKey(CKeyID(uint160(vSolutions[0])), key))
                    {
                        if (f_printcoinstake)
                            LogPrintf("CreateCoinStake : failed to get key for kernel type=%s\n", GetTxnOutputType(whichType));
                        break;  // unable to find corresponding public key
                    }
                    // same as: scriptPubKeyOut << ToByteVector(key.GetPubKey()) << OP_CHECKSIG;
                    scriptPubKeyOut = GetScriptForRawPubKey(key.GetPubKey());
                }
                else
                if(whichType == TX_PUBKEY) {
                    // Copy as is,
                    // output like:
                    // "asm": "026c8805d86bce7a0dd40a0bb5164e071b835beadbccd30fad162130622f7a25be OP_CHECKSIG"
                    scriptPubKeyOut = scriptPubKeyKernel;
                }
                else {
                    // We cannot run minting on TX_MULTISIG or such transaction, since this is
                    // cannot be modified.
                    // Also, other TX types are ignored
                    if (f_printcoinstake)
                        LogPrintf("CreateCoinStake : no support for kernel type=%d:%s\n", whichType, GetTxnOutputType(whichType));
                    break;  // only support pay to public key and pay to address
                }

                txNew.nTime -= n;
                txNew.vin.push_back(CTxIn(pcoin.outpoint));
                nCredit += pcoin.txout.nValue;
                vtxPrev.push_back(tx);
                txNew.vout.push_back(CTxOut(0, scriptPubKeyOut));
                if ((nSplitPos < 0) || (nSplitPos && header.GetBlockTime() + nStakeSplitAge > txNew.nTime && nCredit > nPoWReward))
                    txNew.vout.push_back(CTxOut(0, scriptPubKeyOut)); //split stake if (age < 90 && value > POW)
                if (f_printcoinstake)
                    LogPrintf("CreateCoinStake : added kernel type=%s\n", GetTxnOutputType(whichType));
                fKernelFound = true;
                break;
            }
        }
        if (fKernelFound)
            break; // if kernel is found stop searching
    }
    if (nCredit == 0 || nCredit > nBalance - nReserveBalance)
        return false;

#if 0
    // Disable collect dust into Coinstake TX since 0.8.0, because of:
    // - practically, it almost never happening
    // - dust is useful in DP TX optimizer
    // - after unpack p2sh/p2wsh scriptPubKeyKernel is changed, need control it
    for (const auto& pcoin : setCoins)
    {
        // Attempt to add more inputs
        // Only add coins of the same key/address as kernel
        if (txNew.vout.size() == 2 && ((pcoin.txout.scriptPubKey == scriptPubKeyKernel || pcoin.txout.scriptPubKey == txNew.vout[1].scriptPubKey))
            && pcoin.outpoint.hash != txNew.vin[0].prevout.hash)
        {
            uint256 hashBlock = uint256();
            CTransactionRef tx;
            if (!g_txindex->FindTx(pcoin.outpoint.hash, hashBlock, tx))
                return error("failed to find tx");

            // Stop adding more inputs if already too many inputs
            if (txNew.vin.size() >= 100)
                break;
            // Stop adding more inputs if value is already pretty significant
            if (nCredit > nCombineThreshold)
                break;
            // Stop adding inputs if reached reserve limit
            if (nCredit + pcoin.txout.nValue > nBalance - nReserveBalance)
                break;
            // Do not add additional significant input
            if (pcoin.txout.nValue > nCombineThreshold)
                continue;
            // Do not add input that is still too young
            if (tx->nTime + params.nStakeMaxAge > txNew.nTime)
                continue;
            txNew.vin.push_back(CTxIn(pcoin.outpoint));
            nCredit += pcoin.txout.nValue;
            vtxPrev.push_back(tx);
        }
    }
#endif

    // Calculate coin age reward
    CAmount nReward = 0;
    {
        CCoinsViewCache view(&::ChainstateActive().CoinsTip());
        if (!GetEmc7POSReward(CTransaction(txNew), view, nReward))
            return error("CreateCoinStake() : %s unable to get coin reward for coinstake", txNew.GetHash().ToString());
        if (nReward <= 10 * TX_DP_AMOUNT)
            return false; // Prevent extra small UTXO
        nCredit += nReward;
    }

    CAmount nMinFee = 0;
    while(true)
    {
        // Set output amount
        if (txNew.vout.size() == 3)
        {
            if(nSplitPos < 0) {
                txNew.vout[1].nValue = nReward;
            } else {
                CAmount vout1 = nCredit / 4 + GetRand(nCredit / 2);
                txNew.vout[1].nValue = (vout1 / TX_DP_AMOUNT) * TX_DP_AMOUNT;
            }
            txNew.vout[2].nValue = nCredit - nMinFee - txNew.vout[1].nValue;
        }
        else
            txNew.vout[1].nValue = nCredit - nMinFee;

        // Sign
        int nIn = 0;
        for (const CTransactionRef& tx : vtxPrev)
        {
            if (!SignSignature(*pwallet, *tx, txNew, nIn++, SIGHASH_ALL))
                return error("CreateCoinStake : failed to sign coinstake");
        }

        // Limit size
        unsigned int nBytes = ::GetSerializeSize(txNew, SER_NETWORK, PROTOCOL_VERSION);
        if (nBytes >= 1000000/5)
            return error("CreateCoinStake : exceeded coinstake size limit");

        // Check enough fee is paid
        if (nMinFee < txNew.GetMinFee() - MIN_TX_FEE)
        {
            nMinFee = txNew.GetMinFee() - MIN_TX_FEE;
        if(nMinFee > nCredit)
              return error("CreateCoinStake : Unable to create: nMinFee > nCredit");
            continue; // try signing again
        }
        else
        {
            if (gArgs.GetBoolArg("-printfee", false))
                LogPrintf("CreateCoinStake : fee for coinstake %s\n", FormatMoney(nMinFee));
            break;
        }
    }

    // Successfully generated coinstake
    // Remove block reference from the cache
    delete pbo->value.first;
    pbo->value.first = NULL; // Set "temporary removed"
    CacheBlockOffset.MarkDel(pbo);
    prev_committed_txes = ~0; // Reload coinset next time, after stake
    return true;
}
