// Copyright (c) 2026 The Emercoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// uint256HashMap backs the PoS minter's block cache and the randpay UTXO locks.

#include <test/setup_common.h>
#include <uint256.h>
#include <uint256hm.h>

#include <boost/test/unit_test.hpp>

#include <vector>

BOOST_FIXTURE_TEST_SUITE(uint256hm_tests, BasicTestingSetup)

static std::vector<uint256> Keys(int n)
{
    std::vector<uint256> keys;
    for (int i = 0; i < n; i++)
        keys.push_back(InsecureRand256());
    return keys;
}

static int Count(const uint256HashMap<int>& map)
{
    int n = 0;
    for (auto* p = map.First(); p != nullptr; p = map.Next(p))
        n++;
    return n;
}

BOOST_AUTO_TEST_CASE(insert_search)
{
    uint256HashMap<int> map;
    map.Set(4);
    std::vector<uint256> keys = Keys(100); // grows past the initial size
    for (int i = 0; i < 100; i++)
        map.Insert(keys[i], i);
    BOOST_CHECK_EQUAL(map.size(), 100U);
    for (int i = 0; i < 100; i++) {
        auto* p = map.Search(keys[i]);
        BOOST_REQUIRE(p != nullptr);
        BOOST_CHECK_EQUAL(p->value, i);
    }
    BOOST_CHECK(map.Search(InsecureRand256()) == nullptr);
    BOOST_CHECK_EQUAL(Count(map), 100);
}

// Deleting every cell from the head on, and deleting the tail: the head and Next() stay within
// the table.
BOOST_AUTO_TEST_CASE(delete_all_and_tail)
{
    for (int n : {1, 2, 3, 7}) {
        uint256HashMap<int> map;
        map.Set(8);
        std::vector<uint256> keys = Keys(n);
        for (int i = 0; i < n; i++)
            map.Insert(keys[i], i);

        // delete the tail first, then the rest from the head
        map.MarkDel(map.Search(keys[n - 1]));
        BOOST_CHECK_EQUAL(Count(map), n - 1);
        for (int i = 0; i < n - 1; i++) {
            map.MarkDel(map.Search(keys[i]));
            BOOST_CHECK_EQUAL(Count(map), n - 2 - i);
        }
        BOOST_CHECK_EQUAL(map.size(), 0U);
        BOOST_CHECK(map.First() == nullptr);
        for (int i = 0; i < n; i++)
            BOOST_CHECK(map.Search(keys[i]) == nullptr);

        // the map stays usable for new keys
        int v43 = 43;
        uint256 fresh = InsecureRand256();
        map.Insert(fresh, v43);
        BOOST_CHECK_EQUAL(map.size(), 1U);
        BOOST_CHECK_EQUAL(map.Search(fresh)->value, 43);
    }
}

BOOST_AUTO_TEST_CASE(delete_middle)
{
    uint256HashMap<int> map;
    map.Set(16);
    std::vector<uint256> keys = Keys(10);
    for (int i = 0; i < 10; i++)
        map.Insert(keys[i], i);
    for (int i = 1; i < 10; i += 2)
        map.MarkDel(map.Search(keys[i]));
    BOOST_CHECK_EQUAL(map.size(), 5U);
    BOOST_CHECK_EQUAL(Count(map), 5);
    for (auto* p = map.First(); p != nullptr; p = map.Next(p))
        BOOST_CHECK_EQUAL(p->value % 2, 0);
}

BOOST_AUTO_TEST_SUITE_END()
