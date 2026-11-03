// Copyright (c) 2026 The Emercoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// Difficulty retargeting (PoW and PoS) and the PoW reward, checked against mainnet blocks:
// GetNextTargetRequired() must give each block's nBits from its ancestors, and
// GetProofOfWorkReward() each PoW block's mint. Both run on OpenSSL BIGNUM (CBigNum), so a
// replacement of it, or any change to the retarget rules, shows up here in seconds.

#include <chain.h>
#include <chainparams.h>
#include <pow.h>
#include <test/data/emc_mainnet_headers.json.h>
#include <test/setup_common.h>
#include <univalue.h>
#include <util/strencodings.h>
#include <validation.h>

#include <boost/test/unit_test.hpp>

#include <vector>

extern UniValue read_json(const std::string& jsondata);

namespace {
struct MainnetBlock {
    int height;
    uint32_t time;
    uint32_t bits;
    bool pos;
    CAmount mint;
};

std::vector<MainnetBlock> LoadBlocks()
{
    UniValue rows = read_json(std::string(json_tests::emc_mainnet_headers, json_tests::emc_mainnet_headers + sizeof(json_tests::emc_mainnet_headers)));
    std::vector<MainnetBlock> blocks;
    for (unsigned int i = 0; i < rows.size(); i++) {
        const UniValue& row = rows[i];
        if (row.size() != 5) continue; // comment
        MainnetBlock b;
        b.height = row[0].get_int();
        b.time = row[1].get_int64();
        b.bits = std::stoul(row[2].get_str(), nullptr, 16);
        b.pos = row[3].get_int() != 0;
        b.mint = row[4].get_int64();
        blocks.push_back(b);
    }
    return blocks;
}
} // namespace

BOOST_FIXTURE_TEST_SUITE(emercoin_pow_tests, BasicTestingSetup) // mainnet params

BOOST_AUTO_TEST_CASE(mainnet_next_target)
{
    const Consensus::Params& params = Params().GetConsensus();
    const std::vector<MainnetBlock> rows = LoadBlocks();
    BOOST_REQUIRE(rows.size() > 2000);

    // Contiguous runs of the chain; a run starts where the height jumps.
    std::vector<CBlockIndex> index(rows.size());
    for (size_t i = 0; i < rows.size(); i++) {
        index[i].nHeight = rows[i].height;
        index[i].nTime = rows[i].time;
        index[i].nBits = rows[i].bits;
        index[i].nFlags = rows[i].pos ? BLOCK_PROOF_OF_STAKE : 0;
        index[i].pprev = (i > 0 && rows[i - 1].height == rows[i].height - 1) ? &index[i - 1] : nullptr;
    }

    int checked_pow = 0, checked_pos = 0;
    for (size_t i = 0; i < index.size(); i++) {
        if (!index[i].pprev) continue;
        const bool pos = index[i].IsProofOfStake();
        // GetNextTargetRequired reads the last two blocks of the same kind: both must be in this run
        const CBlockIndex* prev = GetLastBlockIndex(index[i].pprev, pos);
        if (prev->IsProofOfStake() != pos || !prev->pprev) continue;
        const CBlockIndex* prevprev = GetLastBlockIndex(prev->pprev, pos);
        if (prevprev->IsProofOfStake() != pos || !prevprev->pprev) continue;

        BOOST_CHECK_MESSAGE(GetNextTargetRequired(index[i].pprev, pos, params) == index[i].nBits,
                            strprintf("height %d (%s): got %08x, mainnet has %08x", index[i].nHeight, pos ? "PoS" : "PoW",
                                      GetNextTargetRequired(index[i].pprev, pos, params), index[i].nBits));
        ++(pos ? checked_pos : checked_pow);
    }
    // all five runs (early chain, the 6666 and 10000 switches, a mid-chain run, the tip) are exercised
    BOOST_CHECK_GT(checked_pow, 1000);
    BOOST_CHECK_GT(checked_pos, 500);
}

BOOST_AUTO_TEST_CASE(mainnet_pow_reward)
{
    // A block may claim less than the reward: early miners rounded it down to a cent.
    int checked = 0, exact = 0;
    for (const MainnetBlock& b : LoadBlocks()) {
        if (b.pos) continue;
        const CAmount reward = GetProofOfWorkReward(b.bits);
        BOOST_CHECK_MESSAGE(b.mint <= reward && reward - b.mint < CENT,
                            strprintf("height %d bits %08x: reward %d, mainnet minted %d", b.height, b.bits, reward, b.mint));
        ++checked;
        exact += reward == b.mint;
    }
    BOOST_CHECK_GT(checked, 1000);
    BOOST_TEST_MESSAGE(strprintf("PoW blocks: %d, minted exactly the reward: %d", checked, exact));
    BOOST_CHECK_GT(exact, 100); // mainnet data: 132 of 1316
}

BOOST_AUTO_TEST_SUITE_END()
