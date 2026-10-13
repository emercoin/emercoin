#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Check that the test framework speaks Emercoin's serialization.

- Blocks and transactions from the node (RPC hex) deserialize and re-serialize byte for
  byte: transaction nTime, block signature (vchBlockSig).
- A block built in Python, signed by its coinbase P2PK key, is accepted via submitblock
  and via P2P.
- Headers and blocks sent by the node over P2P (with the nFlags PoS marker) are parsed.
"""

from test_framework.blocktools import create_block, create_coinbase
from test_framework.messages import (
    CBlock,
    CInv,
    CTransaction,
    FromHex,
    MSG_WITNESS_FLAG,
    ToHex,
    msg_block,
    msg_getdata,
    msg_getheaders,
)
from test_framework.mininode import P2PInterface
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal


class EmercoinFormatTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        node = self.nodes[0]

        self.log.info("RPC hex round-trip of a node-mined block and its transactions")
        node.sendtoaddress(node.getnewaddress(), 1)
        blockhash = node.generate(1)[0]
        block_hex = node.getblock(blockhash, 0)
        block = FromHex(CBlock(), block_hex)
        block.rehash()
        assert_equal(block.hash, blockhash)
        assert_equal(ToHex(block), block_hex)
        assert len(block.vchBlockSig) > 0
        assert_equal(len(block.vtx), 2)
        for tx in block.vtx:
            tx.rehash()
            tx_hex = node.getrawtransaction(tx.hash, False, blockhash)
            assert_equal(ToHex(tx), tx_hex)
            decoded = node.decoderawtransaction(tx_hex)
            assert_equal(decoded["txid"], tx.hash)
            assert_equal(decoded["time"], tx.nTime)
            assert_equal(ToHex(FromHex(CTransaction(), tx_hex)), tx_hex)

        self.log.info("Python-built block is accepted via submitblock")
        tip = node.getbestblockhash()
        height = node.getblockcount()
        block_time = node.getblock(tip)["time"] + 1
        block = create_block(int(tip, 16), create_coinbase(height + 1), block_time)
        block.solve()
        assert len(block.vchBlockSig) > 0
        assert_equal(node.submitblock(ToHex(block)), None)
        assert_equal(node.getbestblockhash(), block.hash)

        self.log.info("Python-built block is accepted via P2P")
        p2p = node.add_p2p_connection(P2PInterface())
        block2 = create_block(block.sha256, create_coinbase(height + 2), block_time + 1)
        block2.solve()
        p2p.send_and_ping(msg_block(block2))
        assert_equal(node.getbestblockhash(), block2.hash)

        self.log.info("Headers and blocks sent by the node parse over P2P")
        new_hash = node.generate(1)[0]
        getheaders = msg_getheaders()
        getheaders.locator.vHave = [block2.sha256]
        p2p.send_message(getheaders)
        p2p.wait_for_header(int(new_hash, 16))
        header = p2p.last_message["headers"].headers[0]
        assert_equal(header.nFlags & 1, 0)  # PoW block: no BLOCK_PROOF_OF_STAKE flag
        getdata = msg_getdata()
        getdata.inv.append(CInv(2 | MSG_WITNESS_FLAG, int(new_hash, 16)))  # witness block, as getblock returns it
        # P2PInterface may already have fetched the non-witness block after the node's inv;
        # the ping makes sure our witness block is the last one received.
        p2p.send_and_ping(getdata)
        received = p2p.last_message["block"].block
        assert_equal(ToHex(received), node.getblock(new_hash, 0))


if __name__ == '__main__':
    EmercoinFormatTest().main()
