#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Name-value storage (NVS): name_new / name_update / name_delete across nodes.

- A registered name is the same on every node (value, txid, owner, expiry).
- Only the owner can update or delete it; ownership moves with name_update toaddress.
- An active name cannot be registered again; a deleted or expired one can.
- A name lives 175 blocks per rental day; name_update adds its days to the current expiry.
- Name and value length limits.
- Name operations that a block would ignore (not spending the name's last output, name_new on
  an active name) are refused by the mempool; a block that contains one is still valid and
  leaves the name unchanged.
- Non-ASCII text sent as \\uXXXX escapes to a -legacyrpc node is stored as UTF-8, except
  \\u0000-\\u00FF, which stay single bytes.
"""

from test_framework.blocktools import add_witness_commitment, create_block, create_coinbase
from test_framework.messages import COIN, COutPoint, CTransaction, CTxIn, CTxOut, FromHex, ToHex
from test_framework.script import CScript, OP_2DROP, OP_DROP
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_greater_than,
    assert_raises_rpc_error,
)

BLOCKS_PER_DAY = 175
NAMECOIN_TX_VERSION = 0x0666
OP_NAME_NEW, OP_NAME_UPDATE, OP_NAME_DELETE = 1, 2, 3


def name_script(op, name, value, dest_script, days=1):
    """Name output script (createNameScript in namecoin.cpp), value of one chunk."""
    if op == OP_NAME_DELETE:
        return CScript([op, OP_DROP, name, OP_DROP]) + dest_script
    return CScript([op, OP_DROP, name, bytes([days]), OP_2DROP, value, OP_DROP]) + dest_script
MAX_NAME_LENGTH = 512
MAX_VALUE_LENGTH = 20 * 1024


class NamesTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 3
        # node 2 decodes JSON-RPC requests the json_spirit way (the emercoind default)
        self.extra_args = [[], [], ['-legacyrpc=1']]

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def mine(self, node, blocks=1):
        self.sync_all()
        node.generate(blocks)
        self.sync_all()

    def assert_name(self, name, **expected):
        """The name looks the same on every node."""
        shows = [node.name_show(name) for node in self.nodes]
        for show in shows:
            assert_equal(show, shows[0])
        for key, value in expected.items():
            assert_equal(shows[0][key], value)
        return shows[0]

    def run_test(self):
        node0, node1, node2 = self.nodes

        self.log.info("name_new registers a name on every node")
        txid = node0.name_new("test:alpha", "v1", 1)
        self.mine(node0)
        height = node0.getblockcount()
        show = self.assert_name("test:alpha", value="v1", txid=txid)
        assert node0.getaddressinfo(show["address"])["ismine"]
        assert not node1.getaddressinfo(show["address"])["ismine"]
        assert_equal(show["expires_at"], height + BLOCKS_PER_DAY)
        assert "expired" not in show and "deleted" not in show

        self.log.info("An active name cannot be registered again")
        assert_raises_rpc_error(None, "name_new on an unexpired name", node1.name_new, "test:alpha", "x", 1)
        assert_raises_rpc_error(None, "name_new on an unexpired name", node0.name_new, "test:alpha", "x", 1)

        self.log.info("Only the owner can update a name")
        assert_raises_rpc_error(None, "prev name tx is not yours", node1.name_update, "test:alpha", "stolen", 1)
        expires_at = show["expires_at"]
        txid2 = node0.name_update("test:alpha", "v2", 2)
        self.log.info("A name with a pending operation cannot be changed until it is mined")
        assert_raises_rpc_error(None, "pending operations on that name", node0.name_update, "test:alpha", "v3", 1)
        self.mine(node1)
        show = self.assert_name("test:alpha", value="v2", txid=txid2)
        assert_equal(show["expires_at"], expires_at + 2 * BLOCKS_PER_DAY)
        history = node0.name_history("test:alpha")
        assert_equal([op["value"] for op in history], ["v1", "v2"])

        self.log.info("name_update to another address transfers the name")
        new_owner = node1.getnewaddress()
        node0.name_update("test:alpha", "v3", 1, new_owner)
        self.mine(node0)
        self.assert_name("test:alpha", value="v3", address=new_owner)
        assert_raises_rpc_error(None, "prev name tx is not yours", node0.name_update, "test:alpha", "back", 1)
        node1.name_update("test:alpha", "v4", 1)
        self.mine(node0)
        show = self.assert_name("test:alpha", value="v4")
        assert node1.getaddressinfo(show["address"])["ismine"]  # the wallet moves it to a fresh address of its own

        self.log.info("name_delete by the owner; a deleted name can be registered again")
        assert_raises_rpc_error(None, "prev name tx is not yours", node0.name_delete, "test:alpha")
        node1.name_delete("test:alpha")
        self.mine(node0)
        self.assert_name("test:alpha", deleted=True)
        assert_raises_rpc_error(None, "on an inactive name", node1.name_update, "test:alpha", "v5", 1)
        txid = node0.name_new("test:alpha", "reborn", 1)
        self.mine(node0)
        show = self.assert_name("test:alpha", value="reborn", txid=txid)
        assert node0.getaddressinfo(show["address"])["ismine"]

        self.log.info("A name expires %d blocks per rental day after registration" % BLOCKS_PER_DAY)
        node0.name_new("test:short", "brief", 1)
        self.mine(node0)
        expires_at = self.assert_name("test:short")["expires_at"]
        node0.generate(expires_at - node0.getblockcount())
        self.sync_all()
        show = self.assert_name("test:short", value="brief", expires_in=0)
        assert show.get("expired")
        assert_raises_rpc_error(None, "name_new on an unexpired name", node1.name_new, "test:short", "mine now", 1)
        self.mine(node0)
        assert_greater_than(0, self.assert_name("test:short")["expires_in"])
        assert_raises_rpc_error(None, "on an inactive name", node0.name_update, "test:short", "late", 1)
        node1.name_new("test:short", "mine now", 1)
        self.mine(node0)
        show = self.assert_name("test:short", value="mine now")
        assert node1.getaddressinfo(show["address"])["ismine"]

        self.log.info("Name and value length limits")
        node0.name_new("n" * MAX_NAME_LENGTH, "v" * MAX_VALUE_LENGTH, 1)
        self.mine(node0)
        assert_equal(len(self.assert_name("n" * MAX_NAME_LENGTH)["value"]), MAX_VALUE_LENGTH)
        assert_raises_rpc_error(None, None, node0.name_new, "n" * (MAX_NAME_LENGTH + 1), "v", 1)
        assert_raises_rpc_error(None, None, node0.name_new, "test:big", "v" * (MAX_VALUE_LENGTH + 1), 1)
        assert_raises_rpc_error(None, "value must not be empty", node0.name_new, "test:empty", "", 1)

        self.log.info("Name operations a block would ignore are refused by the mempool")
        node0.name_new("test:mempool", "owner", 1)
        self.mine(node0)
        for op, value in [(OP_NAME_UPDATE, b"other"), (OP_NAME_DELETE, b""), (OP_NAME_NEW, b"other")]:
            tx = self.raw_name_tx(node1, op, b"test:mempool", value)
            assert_raises_rpc_error(-26, "bad-name-op", node1.sendrawtransaction, tx)
        assert_equal(node1.getrawmempool(), [])
        node0.name_update("test:mempool", "owner 2", 1)
        self.mine(node0)
        self.assert_name("test:mempool", value="owner 2")

        self.log.info("A block containing such an operation is valid; the name does not change")
        tx = FromHex(CTransaction(), self.raw_name_tx(node1, OP_NAME_UPDATE, b"test:mempool", b"other"))
        tip = node0.getblock(node0.getbestblockhash())
        block_time = max(tip["time"] + 1, tx.nTime)  # no tx may be younger than its block
        block = create_block(int(tip["hash"], 16), create_coinbase(tip["height"] + 1), block_time)
        block.vtx.append(tx)
        add_witness_commitment(block)  # the wallet may have funded the tx from a segwit output
        block.solve()
        assert_equal(node0.submitblock(ToHex(block)), None)
        self.sync_all()
        assert_equal(node1.getbestblockhash(), block.hash)
        show = self.assert_name("test:mempool", value="owner 2")
        assert node0.getaddressinfo(show["address"])["ismine"]

        self.log.info("Non-ASCII text sent as \\uXXXX escapes to a -legacyrpc node is stored as UTF-8")
        name, value = "test:имя", "значение 😀 €"
        # AuthServiceProxy sends json.dumps(ensure_ascii=True): every non-ASCII character as \\uXXXX
        node2.name_new(name, value, 1)
        self.mine(node0)
        show = node0.name_show(name, "hex")
        assert_equal(bytes.fromhex(show["value"]), value.encode())
        assert_equal(node1.name_show(name)["value"], value)
        assert_equal(node0.name_show(name)["name"], name)
        # \u0000-\u00FF stay single bytes in legacy mode (the json_spirit convention for binary
        # values), so Latin-1 text sent escaped is not UTF-8: this also proves node 2 is legacy
        node2.name_new("test:latin", "\u00e9", 1)
        self.mine(node0)
        assert_equal(node0.name_show("test:latin", "hex")["value"], "e9")


    def raw_name_tx(self, node, op, name, value):
        """A name tx funded and signed by `node` that does not spend the name's output."""
        utxo = next(u for u in node.listunspent() if u["amount"] >= 1)
        dest = CScript(bytes.fromhex(node.getaddressinfo(node.getnewaddress("", "legacy"))["scriptPubKey"]))
        tx = CTransaction()
        tx.nVersion = NAMECOIN_TX_VERSION
        tx.vin = [CTxIn(COutPoint(int(utxo["txid"], 16), utxo["vout"]))]
        amount = int(round(utxo["amount"] * COIN))
        tx.vout = [CTxOut(COIN // 100, name_script(op, name, value, dest)), CTxOut(amount - 2 * (COIN // 100), dest)]
        signed = node.signrawtransactionwithwallet(ToHex(tx))
        assert signed["complete"]
        return signed["hex"]


if __name__ == '__main__':
    NamesTest().main()
