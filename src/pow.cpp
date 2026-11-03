// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <pow.h>

#include <arith_uint256.h>
#include <chain.h>
#include <primitives/block.h>
#include <uint256.h>

#include <bignum.h>
#include <auxpow.h>
#include <util/system.h>
#include <consensus/merkle.h>
#include <util/strencodings.h>

unsigned int GetNextTargetRequired(const CBlockIndex* pindexLast, bool fProofOfStake, const Consensus::Params& params)
{
    using namespace std;

    if (pindexLast == NULL)
        return UintToArith256(params.powLimit).GetCompact(); // genesis block

    if (params.fPowNoRetargeting)
        return UintToArith256(params.bnInitialHashTarget).GetCompact();

    const CBlockIndex* pindexPrev = GetLastBlockIndex(pindexLast, fProofOfStake);
    if (pindexPrev->pprev == NULL)
        return UintToArith256(params.bnInitialHashTarget).GetCompact(); // first block
    const CBlockIndex* pindexPrevPrev = GetLastBlockIndex(pindexPrev->pprev, fProofOfStake);
    if (pindexPrevPrev->pprev == NULL)
        return UintToArith256(params.bnInitialHashTarget).GetCompact(); // second block

    int64_t nActualSpacing = pindexPrev->GetBlockTime() - pindexPrevPrev->GetBlockTime();

    // ppcoin: target change every block
    // ppcoin: retarget with exponential moving toward target spacing
    CBigNum bnNew;
    bnNew.SetCompact(pindexPrev->nBits);

    // emercoin: first 10 000 blocks are faster to mine.
    int64_t nSpacingRatio = (pindexLast->nHeight <= 10000) ? max((int64_t)10, params.nStakeTargetSpacing * pindexLast->nHeight / 10000) :
                                                             max((int64_t)10, params.nStakeTargetSpacing);

    int64_t nTargetSpacing = fProofOfStake? params.nStakeTargetSpacing : min(params.nTargetSpacingMax, nSpacingRatio * (1 + pindexLast->nHeight - pindexPrev->nHeight));
    int64_t nInterval = params.nTargetTimespan / nTargetSpacing;

    int n = fProofOfStake ? 1 : ((pindexLast->nHeight < 6666) ? 1 : 3);
    bnNew *= ((nInterval - n) * nTargetSpacing + (n + 1) * nActualSpacing);
    bnNew /= ((nInterval + 1) * nTargetSpacing);

    if (bnNew > CBigNum(params.powLimit))
        bnNew = CBigNum(params.powLimit);

    return bnNew.GetCompact();
}

bool CheckProofOfWork(uint256 hash, unsigned int nBits, const Consensus::Params& params)
{
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(params.powLimit))
        return false;

    // Check proof of work matches claimed amount
    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
}

unsigned char pchMergedMiningHeader[] = { 0xfa, 0xbe, 'm', 'm' };

bool AuxPoWCheck(const CAuxPow& aux, const uint256& hashAuxBlock, int nChainID, const Consensus::Params& params)
{
    if (aux.nIndex != 0)
        return error("AuxPow is not a generate");

    if (!params.fPowAllowMinDifficultyBlocks && aux.parentBlockHeader.GetChainID() == nChainID)
        return error("Aux POW parent has our chain ID");

    if (aux.vChainMerkleBranch.size() > 30)
        return error("Aux POW chain merkle branch too long");

    // Check that the chain merkle root is in the coinbase
    uint256 nRootHash = ComputeMerkleRootFromBranch(hashAuxBlock, aux.vChainMerkleBranch, aux.nChainIndex);
    std::vector<unsigned char> vchRootHash(nRootHash.begin(), nRootHash.end());
    std::reverse(vchRootHash.begin(), vchRootHash.end()); // correct endian

    // Check that we are in the parent block merkle tree
    if (ComputeMerkleRootFromBranch(aux.tx->GetBtcHash(), aux.vMerkleBranch, aux.nIndex) != aux.parentBlockHeader.hashMerkleRoot)
        return error("Aux POW merkle root incorrect");

    const CScript script = aux.tx->vin[0].scriptSig;

    // Check that the same work is not submitted twice to our chain.
    //

    CScript::const_iterator pcHead =
        std::search(script.begin(), script.end(), UBEGIN(pchMergedMiningHeader), UEND(pchMergedMiningHeader));

    CScript::const_iterator pc =
        std::search(script.begin(), script.end(), vchRootHash.begin(), vchRootHash.end());

    if (pcHead == script.end())
        return error("MergedMiningHeader missing from parent coinbase");

    if (pc == script.end())
        return error("Aux POW missing chain merkle root in parent coinbase");

    if (pcHead != script.end())
    {
        // Enforce only one chain merkle root by checking that a single instance of the merged
        // mining header exists just before.
        if (script.end() != std::search(pcHead + 1, script.end(), UBEGIN(pchMergedMiningHeader), UEND(pchMergedMiningHeader)))
            return error("Multiple merged mining headers in coinbase");
        if (pcHead + sizeof(pchMergedMiningHeader) != pc)
            return error("Merged mining header is not just before chain merkle root");
    }
    else
    {
        // For backward compatibility.
        // Enforce only one chain merkle root by checking that it starts early in the coinbase.
        // 8-12 bytes are enough to encode extraNonce and nBits.
        if (pc - script.begin() > 20)
            return error("Aux POW chain merkle root must start in the first 20 bytes of the parent coinbase");
    }


    // Ensure we are at a deterministic point in the merkle leaves by hashing
    // a nonce and our chain ID and comparing to the index.
    pc += vchRootHash.size();
    if (script.end() - pc < 8)
        return error("Aux POW missing chain merkle tree size and nonce in parent coinbase");

    int nSize;
    memcpy(&nSize, &pc[0], 4);
    if (nSize != (1 << aux.vChainMerkleBranch.size()))
        return error("Aux POW merkle branch size does not match parent coinbase");

    int nNonce;
    memcpy(&nNonce, &pc[4], 4);

    // Choose a pseudo-random slot in the chain merkle tree
    // but have it be fixed for a size/nonce/chain combination.
    //
    // This prevents the same work from being used twice for the
    // same chain while reducing the chance that two chains clash
    // for the same slot.
    unsigned int rand = nNonce;
    rand = rand * 1103515245 + 12345;
    rand += nChainID;
    rand = rand * 1103515245 + 12345;

    if (aux.nChainIndex != (rand % nSize))
        return error("Aux POW wrong index");

    return true;
}

bool CheckBlockProofOfWork(const CBlockHeader *pblock, const Consensus::Params& params)
{
    // There's an issue with blocks prior to the auxpow fork reporting an invalid chain ID.
    // As no version earlier than the 0.10 client a) has version 5+ blocks and b)
    //	has auxpow, anything that isn't a version 5+ block can be checked normally.

    if (pblock->GetBlockVersion() > 4)
    {
        if (!params.fPowAllowMinDifficultyBlocks && (pblock->nVersion & BLOCK_VERSION_AUXPOW && pblock->GetChainID() != AUXPOW_CHAIN_ID))
            return error("CheckBlockProofOfWork() : block does not have our chain ID");

        if (pblock->auxpow.get() != NULL)
        {
            if (!AuxPoWCheck(*pblock->auxpow, pblock->GetHash(), pblock->GetChainID(), params))
                return error("CheckBlockProofOfWork() : AUX POW is not valid");
            // Check proof of work matches claimed amount
            if (!CheckProofOfWork(pblock->auxpow->GetParentBlockHash(), pblock->nBits, params))
                return error("CheckBlockProofOfWork() : AUX proof of work failed");
        }
        else
        {
            // Check proof of work matches claimed amount
            if (!CheckProofOfWork(pblock->GetHash(), pblock->nBits, params))
                return error("CheckBlockProofOfWork() : proof of work failed");
        }
    }
    else
    {
        // Check proof of work matches claimed amount
        if (!CheckProofOfWork(pblock->GetHash(), pblock->nBits, params))
            return error("CheckBlockProofOfWork() : proof of work failed");
    }
    return true;
}
