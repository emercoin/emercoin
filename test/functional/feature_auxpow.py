#!/usr/bin/env python3
# Copyright (c) 2026 The Emercoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Merged mining (auxpow) through getauxblock, the way pools mine Emercoin PoW blocks.

- getauxblock returns work: the hash of a block template, its target and our chain ID.
- A parent block whose coinbase commits to that hash (merged mining header 0xfabe6d6d,
  hash, tree size, nonce) and whose header meets the target solves it: the block is
  accepted, carries the auxpow version bit, and reaches the other node over P2P.
- Rejected: no merged mining header, a commitment to another hash, a parent header
  above the target, unknown work.
"""

import struct

from test_framework.messages import (
    BLOCK_VERSION_AUXPOW,
    CBlockHeader,
    COutPoint,
    CTxIn,
    CTxOut,
    hash256,
    ser_uint256,
    ser_vector,
    uint256_from_str,
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
)

MERGED_MINING_HEADER = b"\xfa\xbe\x6d\x6d"
AUXPOW_CHAIN_ID = 666


def btc_coinbase(script_sig):
    """A parent-chain coinbase, serialized the Bitcoin way (no nTime), as pools send it."""
    vin = [CTxIn(COutPoint(0, 0xffffffff), script_sig, 0xffffffff)]
    vout = [CTxOut(50 * 10**8, b"\x51")]
    return struct.pack("<i", 1) + ser_vector(vin) + ser_vector(vout) + struct.pack("<I", 0)


def make_auxpow(aux_hash_hex, target, commit=True, marker=True, solve=True):
    """Serialized CAuxPow (getauxblock format) for the aux block hash; chain merkle tree of one leaf."""
    script_sig = b"\x03\x01\x00\x00"  # parent height
    if marker:
        script_sig += MERGED_MINING_HEADER
    root = bytes.fromhex(aux_hash_hex) if commit else bytes(32)  # big-endian, as displayed
    script_sig += root + struct.pack("<I", 1) + struct.pack("<I", 0)  # tree size 1, nonce 0
    coinbase = btc_coinbase(script_sig)

    parent = CBlockHeader()
    parent.nVersion = 1  # another chain ID than ours
    parent.hashPrevBlock = 0
    parent.hashMerkleRoot = uint256_from_str(hash256(coinbase))
    parent.nTime = 1700000000
    parent.nBits = 0x207fffff
    parent.nNonce = 0
    parent.rehash()
    while (parent.sha256 <= target) != solve:
        parent.nNonce += 1
        parent.rehash()

    auxpow = coinbase
    auxpow += ser_uint256(0)          # hashBlock (unused)
    auxpow += ser_vector([])          # merkle branch of the coinbase in the parent block: it is the only tx
    auxpow += struct.pack("<i", 0)    # nIndex: the coinbase
    auxpow += ser_vector([])          # chain merkle branch: we are the only chain
    auxpow += struct.pack("<I", 0)    # nChainIndex
    auxpow += parent.serialize_header()
    return auxpow.hex()


class AuxpowTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 2

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def get_work(self, node):
        work = node.getauxblock()
        assert_equal(work["chainid"], AUXPOW_CHAIN_ID)
        target = int.from_bytes(bytes.fromhex(work["target"]), "little")
        return work["hash"], target

    def run_test(self):
        node0, node1 = self.nodes

        self.log.info("A parent block committing to the work solves it")
        height = node0.getblockcount()
        aux_hash, target = self.get_work(node0)
        assert_equal(node0.getauxblock(aux_hash, make_auxpow(aux_hash, target)), True)
        assert_equal(node0.getblockcount(), height + 1)
        tip = node0.getbestblockhash()
        assert_equal(tip, aux_hash)
        block = node0.getblock(tip)
        assert block["version"] & BLOCK_VERSION_AUXPOW
        assert_equal(block["version"] >> 16, AUXPOW_CHAIN_ID)
        assert block["flags"].startswith("proof-of-work")

        self.log.info("The auxpow block reaches the other node over P2P")
        self.sync_all()
        assert_equal(node1.getbestblockhash(), tip)
        assert_equal(node1.getblock(tip, 0), node0.getblock(tip, 0))

        self.log.info("Submitting the same work again is a duplicate")
        assert_equal(node0.getauxblock(aux_hash, make_auxpow(aux_hash, target)), "duplicate")

        self.log.info("Invalid proofs are rejected")
        aux_hash, target = self.get_work(node0)
        assert_raises_rpc_error(-100, "CheckBlock", node0.getauxblock, aux_hash, make_auxpow(aux_hash, target, marker=False))
        assert_raises_rpc_error(-100, "CheckBlock", node0.getauxblock, aux_hash, make_auxpow(aux_hash, target, commit=False))
        assert_raises_rpc_error(-100, "CheckBlock", node0.getauxblock, aux_hash, make_auxpow(aux_hash, target, solve=False))
        assert_equal(node0.getblockcount(), height + 1)

        self.log.info("Unknown work is refused")
        assert_equal(node0.getauxblock("00" * 32, make_auxpow("00" * 32, target)), False)

        self.log.info("The same work can still be solved afterwards")
        assert_equal(node0.getauxblock(aux_hash, make_auxpow(aux_hash, target)), True)
        self.sync_all()
        assert_equal(node1.getbestblockhash(), aux_hash)


if __name__ == '__main__':
    AuxpowTest().main()
