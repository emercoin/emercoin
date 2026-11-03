#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""When the node asks STUN servers for its external IPv4 address.

STUN is address discovery: it follows -discover (which -proxy turns off by default) and needs
IPv4 to be reachable. Regtest has no DNS seeds, so the seed thread gets to the STUN step right
after startup. Only cases where STUN is not used are run: the test never contacts a STUN server.
"""
import os

from test_framework.test_framework import BitcoinTestFramework

NOT_USED = "STUN not used: -discover is off or IPv4 is not reachable"
REQUEST = "GetExternalIPbySTUN("


class StunTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.setup_clean_chain = True

    def check_not_used(self, args):
        node = self.nodes[0]
        debug_log = os.path.join(node.datadir, node.chain, "debug.log")
        start = os.path.getsize(debug_log)
        with node.assert_debug_log([NOT_USED], timeout=10):
            self.restart_node(0, ["-dnsseed=1"] + args)
        with open(debug_log, encoding="utf-8") as f:
            f.seek(start)
            assert REQUEST not in f.read(), "STUN request with {}".format(args)

    def run_test(self):
        # The framework writes discover=0 into every node's config; without it -discover takes
        # its default, as for a user, and -proxy has to turn it off by itself.
        self.stop_node(0)
        conf = os.path.join(self.nodes[0].datadir, "emercoin.conf")
        with open(conf, encoding="utf-8") as f:
            lines = [line for line in f if line.strip() != "discover=0"]
        with open(conf, "w", encoding="utf-8") as f:
            f.writelines(lines)
        self.start_node(0)

        self.log.info("-proxy: -discover is off by default, no STUN")
        self.check_not_used(["-proxy=127.0.0.1:1"])

        self.log.info("-onlynet=ipv6: IPv4 is not reachable, no STUN")
        self.check_not_used(["-onlynet=ipv6"])

        self.log.info("-discover=0: no STUN")
        self.check_not_used(["-discover=0"])


if __name__ == '__main__':
    StunTest().main()
