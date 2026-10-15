#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Check that an INV with several unknown blocks is answered with one GETHEADERS.

The node asks for the headers up to the last announced block only.
"""

from test_framework.messages import CInv, msg_inv
from test_framework.mininode import P2PInterface, mininode_lock
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal


class P2PCountGetheaders(P2PInterface):
    def __init__(self):
        super().__init__()
        self.getheaders = []

    def on_getheaders(self, message):
        self.getheaders.append(message)


class InvGetheadersTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1

    def run_test(self):
        node = self.nodes[0]
        peer = node.add_p2p_connection(P2PCountGetheaders())
        peer.sync_with_ping()
        with mininode_lock:
            peer.getheaders.clear()  # the node may start its own header sync with a new peer

        unknown = [0x1000 + i for i in range(10)]
        peer.send_and_ping(msg_inv([CInv(2, h) for h in unknown]))  # 2 = MSG_BLOCK
        with mininode_lock:
            assert_equal(len(peer.getheaders), 1)
            assert_equal(peer.getheaders[0].hashstop, unknown[-1])


if __name__ == '__main__':
    InvGetheadersTest().main()
