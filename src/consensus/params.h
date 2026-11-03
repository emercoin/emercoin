// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2018 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CONSENSUS_PARAMS_H
#define BITCOIN_CONSENSUS_PARAMS_H

#include <uint256.h>
#include <limits>
#include <map>
#include <string>

namespace Consensus {

/**
 * Parameters that influence chain consensus.
 */
struct Params {
    uint256 hashGenesisBlock;
    /* Block hash that is excepted from BIP16 enforcement */
    uint256 BIP16Exception;
    /** Block height and hash at which BIP34 becomes active */
    int BIP34Height;
    uint256 BIP34Hash;
    /** Block height at which BIP65 becomes active */
    int BIP65Height;
    /** Block height at which BIP66 becomes active */
    int BIP66Height;
    /** Block height at which CSV (BIP68, BIP112 and BIP113) becomes active */
    int CSVHeight;
    /** Block height at which Segwit (BIP141, BIP143 and BIP147) becomes active.
     * Note that segwit v0 script rules are enforced on all blocks except the
     * BIP 16 exception blocks. */
    int SegwitHeight;
    /** Block height at which merged mining becomes active */
    int MMHeight;
    /**
     * Minimum blocks including miner confirmation of the total of 2016 blocks in a retargeting period,
     * (nPowTargetTimespan / nPowTargetSpacing) which is also used for BIP9 deployments.
     * Examples: 1916 for 95%, 1512 for testchains.
     */
    uint32_t nRuleChangeActivationThreshold;
    uint32_t nMinerConfirmationWindow;
    /** Proof of work parameters */
    uint256 powLimit;
    bool fPowAllowMinDifficultyBlocks;
    /** emercoin: regtest keeps every block at bnInitialHashTarget, so tests can build blocks with fixed nBits */
    bool fPowNoRetargeting{false};
    int64_t nTargetSpacing;
    int64_t nTargetTimespan;
    uint256 nMinimumChainTrust;
    uint256 defaultAssumeValid;

    // emercoin stuff:
    uint256 bnInitialHashTarget;
    int64_t nStakeTargetSpacing;
    int64_t nTargetSpacingMax;
    int64_t nStakeMinAge;
    int64_t nStakeMaxAge;
    int64_t nStakeModifierInterval;

    /** Used to check majorities for block version upgrade */
    int nRejectBlockOutdatedMajority;
    int nToCheckBlockUpgradeMajority;

    /** Coinbase transaction outputs can only be spent after this number of new blocks (network rule) */
    int nCoinbaseMaturity;
    int nCoinbaseMaturityOld;
};
} // namespace Consensus

#endif // BITCOIN_CONSENSUS_PARAMS_H
