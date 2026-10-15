#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Check blocks whose header fails the checks against its parent.

A block on top of the tip with an outdated version, a timestamp not after the median time
past, or wrong difficulty bits is rejected via P2P and via submitblock: the tip stays, the
header is not stored, and the node keeps serving RPC.
"""

from test_framework.blocktools import AUXPOW_CHAIN_ID, create_block, create_coinbase
from test_framework.messages import ToHex, msg_block
from test_framework.mininode import P2PInterface
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal, assert_raises_rpc_error


class BlockHeaderChecksTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        # rejected blocks must not get the test's own peer banned
        self.extra_args = [["-whitelist=127.0.0.1"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        node = self.nodes[0]
        p2p = node.add_p2p_connection(P2PInterface())
        tip = node.getblock(node.getbestblockhash())

        def block_on_tip(ntime=tip["time"] + 1, version=None, nbits=None):
            block = create_block(int(tip["hash"], 16), create_coinbase(tip["height"] + 1), ntime)
            if version is not None:
                block.nVersion = version
            if nbits is not None:
                block.nBits = nbits
            block.solve()
            return block

        cases = [
            ("bad-version", block_on_tip(version=4 | (AUXPOW_CHAIN_ID << 16))),
            ("time-too-old", block_on_tip(ntime=tip["mediantime"])),
            ("bad-diffbits", block_on_tip(nbits=0x1f7fffff)),  # 256 times harder than expected
        ]
        for reason, block in cases:
            self.log.info("Block with %s is rejected via P2P" % reason)
            with node.assert_debug_log(["AcceptBlock FAILED (%s" % reason], timeout=10):
                p2p.send_message(msg_block(block))
            p2p.sync_with_ping()
            assert_equal(node.getbestblockhash(), tip["hash"])
            assert_raises_rpc_error(-5, "Block not found", node.getblockheader, block.hash)

            self.log.info("Block with %s is rejected via submitblock" % reason)
            assert node.submitblock(ToHex(block)).startswith(reason)
            assert_equal(node.getbestblockhash(), tip["hash"])

        self.log.info("A valid block on the same tip is still accepted")
        block = block_on_tip()
        p2p.send_and_ping(msg_block(block))
        assert_equal(node.getbestblockhash(), block.hash)


if __name__ == '__main__':
    BlockHeaderChecksTest().main()
