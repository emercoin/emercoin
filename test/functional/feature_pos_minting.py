#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Proof-of-stake minting on regtest.

- Coins younger than nStakeMinAge (1 day on regtest) do not mint.
- Once they are old enough, the -stakegen minter of node 0 creates a proof-of-stake block:
  coinbase without value, coinstake as the second transaction, a stake reward, a signature.
- The other node accepts it, and both agree on the chain afterwards.
"""

import time

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_greater_than,
    wait_until,
)

STAKE_MIN_AGE = 24 * 60 * 60     # regtest nStakeMinAge
BLOCK_STEP = 5 * 60              # spacing of the PoW blocks built below
SPREAD_BLOCKS = 30               # 2.5 h of chain time: beyond the 1.2 h stake modifier selection interval


class PoSMintingTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.extra_args = [
            ['-stakegen=1', '-staketimio=200', '-maxtipage=100000000'],
            ['-stakegen=0', '-maxtipage=100000000'],
        ]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def set_time(self, t):
        for node in self.nodes:
            node.setmocktime(t)

    def pos_blocks(self, node):
        tip = node.getblockcount()
        return [h for h in range(1, tip + 1)
                if node.getblock(node.getblockhash(h))["flags"].startswith("proof-of-stake")]

    def run_test(self):
        node0, node1 = self.nodes
        assert_greater_than(node0.getbalance(), 0)

        self.log.info("Spread PoW blocks over time, so that stake modifiers get generated")
        t = node0.getblock(node0.getbestblockhash())["time"]
        for _ in range(SPREAD_BLOCKS):
            t += BLOCK_STEP
            self.set_time(t)
            node1.generate(1)
        self.sync_all()
        tip_height = node0.getblockcount()

        self.log.info("Coins younger than nStakeMinAge do not mint")
        time.sleep(3)
        assert_equal(node0.getblockcount(), tip_height)
        assert_equal(self.pos_blocks(node0), [])

        self.log.info("Once the coins are older than nStakeMinAge, node 0 mints a PoS block")
        t += STAKE_MIN_AGE + BLOCK_STEP
        self.set_time(t)
        # CreateCoinStake caches the wallet's coins and drops those more than a day from maturity
        # (all of them at start on regtest); a wallet transaction makes it reload them. While that
        # transaction is unconfirmed the reload fails (it selects the whole trusted balance,
        # including unconfirmed change), so confirm it with a PoW block first.
        node0.sendtoaddress(node0.getnewaddress(), 1)
        self.sync_all()
        t += 1
        self.set_time(t)
        node1.generate(1)
        self.sync_all()
        tip_height = node0.getblockcount()
        # the minter searches again only when the (mock) clock has moved on
        for _ in range(240):
            t += 1
            self.set_time(t)
            time.sleep(0.25)
            if node0.getblockcount() > tip_height:
                break
        assert_greater_than(node0.getblockcount(), tip_height)
        self.sync_all()

        pos = self.pos_blocks(node0)
        assert_greater_than(len(pos), 0)
        block = node0.getblock(node0.getblockhash(pos[0]), 2)
        coinbase, coinstake = block["tx"][0], block["tx"][1]
        assert_equal(sum(out["value"] for out in coinbase["vout"]), 0)
        assert "coinbase" not in coinstake["vin"][0]
        assert_equal(coinstake["vout"][0]["scriptPubKey"]["type"], "nonstandard")  # empty marker output
        assert_equal(coinstake["vout"][0]["value"], 0)
        assert_greater_than(block["mint"], 0)

        self.log.info("Node 1 accepted the PoS block; both nodes agree")
        assert_equal(node1.getbestblockhash(), node0.getbestblockhash())
        assert_equal(self.pos_blocks(node1), pos)
        info = node1.getblock(node1.getblockhash(pos[0]))
        assert_equal(info["proofhash"], block["proofhash"])

        self.log.info("PoW blocks still extend the chain after PoS blocks")
        node0_tip = node0.getblockcount()
        t += BLOCK_STEP
        self.set_time(t)
        node1.generate(1)
        self.sync_all()
        assert_greater_than(node0.getblockcount(), node0_tip)


if __name__ == '__main__':
    PoSMintingTest().main()
