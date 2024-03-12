// Copyright (c) 2012-2013 The PPCoin developers
// Distributed under the GPL3 software license, see the accompanying
// file COPYING or http://www.gnu.org/licenses/gpl.html.
#ifndef PPCOIN_KERNEL_H
#define PPCOIN_KERNEL_H

#include <memory>

class CBlockHeader;
class CBlockIndex;
class COutPoint;
class CValidationState;
class uint256;
class CWallet;
class CMutableTransaction;

class CTransaction;
typedef std::shared_ptr<const CTransaction> CTransactionRef;

// MODIFIER_INTERVAL_RATIO:
// ratio of group interval length between the last group and the first group
static const int MODIFIER_INTERVAL_RATIO = 3;

// Compute the hash modifier for proof-of-stake
bool ComputeNextStakeModifier(const CBlockIndex* pindexCurrent, uint64_t& nStakeModifier, bool& fGeneratedStakeModifier);

// Check kernel hash target and coinstake signature
// Sets hashProofOfStake on success return
bool CheckProofOfStake(CValidationState& state, CBlockIndex* pindexPrev, const CTransactionRef& tx, unsigned int nBits, uint256& hashProofOfStake);

// Check whether the coinstake timestamp meets protocol
bool CheckCoinStakeTimestamp(int64_t nTimeBlock, int64_t nTimeTx);

// Get stake modifier checksum
unsigned int GetStakeModifierChecksum(const CBlockIndex* pindex);

// Check stake modifier hard checkpoints
bool CheckStakeModifierCheckpoints(int nHeight, unsigned int nStakeModifierChecksum);

bool CreateCoinStake(CWallet* pwallet, unsigned int nBits, int64_t nSearchInterval, CMutableTransaction &txNew);

#endif // PPCOIN_KERNEL_H
