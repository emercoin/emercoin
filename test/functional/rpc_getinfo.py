#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""getinfo with and without a wallet.

- With a wallet, getinfo reports the node fields and the wallet fields.
- Without one (-disablewallet), it reports the node fields only, and the node keeps running.
"""

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import assert_equal

NODE_FIELDS = {"fullversion", "version", "protocolversion", "blocks", "moneysupply", "timeoffset",
               "connections", "proxy", "pow-difficulty", "pos-difficulty", "testnet", "relayfee", "errors"}
WALLET_FIELDS = {"walletversion", "balance", "newmint", "stake", "keypoololdest", "keypoolsize",
                 "unlocked_until", "paytxfee", "encrypted", "mintonly"}


class GetInfoTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2
        self.setup_clean_chain = True  # the cached chain is spread with submitblock, which needs a wallet
        self.extra_args = [[], ["-disablewallet"]]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def run_test(self):
        self.log.info("With a wallet: node and wallet fields")
        info = self.nodes[0].getinfo()
        assert NODE_FIELDS <= set(info), NODE_FIELDS - set(info)
        assert_equal(set(info) & WALLET_FIELDS, WALLET_FIELDS - {"unlocked_until"})  # not encrypted
        assert_equal(info["encrypted"], False)

        self.log.info("Without a wallet: node fields only, and the node keeps running")
        info = self.nodes[1].getinfo()
        assert NODE_FIELDS <= set(info), NODE_FIELDS - set(info)
        assert_equal(set(info) & WALLET_FIELDS, set())
        assert_equal(self.nodes[1].getblockcount(), self.nodes[0].getblockcount())


if __name__ == '__main__':
    GetInfoTest().main()
