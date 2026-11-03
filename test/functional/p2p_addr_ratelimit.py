#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Check the rate limit on addresses received in addr messages (as in Bitcoin Core 22).

An inbound peer starts with one token and gains 0.1 per second; addresses beyond the tokens
are dropped and counted in getpeerinfo's addr_rate_limited. A peer with the `addr`
permission is not limited. Adapted from Bitcoin Core's p2p_addr_relay.py.
"""

import random
import time

from test_framework.messages import CAddress, NODE_NETWORK, NODE_WITNESS, msg_addr
from test_framework.mininode import P2PInterface
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal


class AddrReceiver(P2PInterface):
    def on_addr(self, message):
        pass


class AddrRateLimitTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.setup_clean_chain = True

    def addr_msg(self, num):
        msg = msg_addr()
        for i in range(num):
            addr = CAddress()
            addr.time = self.mocktime + i
            addr.nServices = NODE_NETWORK | NODE_WITNESS
            addr.ip = "%d.%d.%d.%d" % (random.randrange(128, 169), random.randrange(1, 255),
                                       random.randrange(1, 255), random.randrange(1, 255))
            addr.port = 6661
            msg.addrs.append(addr)
        return msg

    def send_and_check(self, peer, num, processed, rate_limited):
        peer.send_and_ping(self.addr_msg(num))
        peerinfo = self.nodes[0].getpeerinfo()[0]
        assert_equal(peerinfo['addr_processed'], processed)
        assert_equal(peerinfo['addr_rate_limited'], rate_limited)

    def run_test(self):
        node = self.nodes[0]
        self.mocktime = int(time.time())
        node.setmocktime(self.mocktime)

        self.log.info("An inbound peer has one token: the rest of 600 addresses is dropped")
        peer = node.add_p2p_connection(AddrReceiver())
        self.send_and_check(peer, 600, 1, 599)
        self.send_and_check(peer, 600, 1, 1199)
        self.send_and_check(peer, 10, 1, 1209)

        self.log.info("100 seconds later 10 more addresses are processed, 1000 seconds later 100 more")
        self.mocktime += 100
        node.setmocktime(self.mocktime)
        self.send_and_check(peer, 200, 11, 1399)
        self.mocktime += 1000
        node.setmocktime(self.mocktime)
        self.send_and_check(peer, 200, 111, 1499)
        node.disconnect_p2ps()

        self.log.info("A peer with the addr permission is not rate limited")
        self.restart_node(0, ["-whitelist=addr@127.0.0.1"])
        node.setmocktime(self.mocktime)
        peer = node.add_p2p_connection(AddrReceiver())
        assert "addr" in node.getpeerinfo()[0]["permissions"]
        self.send_and_check(peer, 600, 600, 0)


if __name__ == '__main__':
    AddrRateLimitTest().main()
