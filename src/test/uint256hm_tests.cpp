// Copyright (c) 2026 The Emercoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// uint256HashMap backs the PoS minter's block cache and the randpay UTXO locks.

#include <test/setup_common.h>
#include <uint256.h>
#include <uint256hm.h>

#include <boost/test/unit_test.hpp>

#include <map>
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

// A cell deleted while at the head of the list and then reused by Insert() must stay in the
// list, so that a rehash (which walks the list) keeps it.
BOOST_AUTO_TEST_CASE(reuse_after_delete_kept_on_rehash)
{
    uint256HashMap<int> map;
    map.Set(8);
    std::vector<uint256> keys = Keys(7);
    for (int i = 0; i < 3; i++)
        map.Insert(keys[i], i);
    map.MarkDel(map.Search(keys[0])); // the head moves past keys[0]'s cell
    int v = 100;
    map.Insert(keys[0], v);           // reuses that cell
    BOOST_CHECK(map.Search(keys[0]) != nullptr);
    BOOST_CHECK_EQUAL(Count(map), 3);
    for (int i = 3; i < 7; i++)       // the table grows: rehash
        map.Insert(keys[i], i);
    BOOST_REQUIRE(map.Search(keys[0]) != nullptr);
    BOOST_CHECK_EQUAL(map.Search(keys[0])->value, 100);
    BOOST_CHECK_EQUAL(map.size(), 7U);
    BOOST_CHECK_EQUAL(Count(map), 7);
}

// Appending after a deleted tail must not bring the deleted entry back.
BOOST_AUTO_TEST_CASE(deleted_tail_stays_deleted)
{
    uint256HashMap<int> map;
    map.Set(16);
    std::vector<uint256> keys = Keys(3);
    for (int i = 0; i < 2; i++)
        map.Insert(keys[i], i);
    map.MarkDel(map.Search(keys[1])); // the tail; keys[0] keeps the head in place
    int two = 2;
    map.Insert(keys[2], two);
    BOOST_CHECK(map.Search(keys[1]) == nullptr);
    BOOST_CHECK_EQUAL(map.size(), 2U);
    BOOST_CHECK_EQUAL(Count(map), 2);
}

BOOST_AUTO_TEST_CASE(insert_existing_key_updates)
{
    uint256HashMap<int> map;
    map.Set(8);
    uint256 key = InsecureRand256();
    int one = 1, two = 2;
    map.Insert(key, one);
    map.Insert(key, two);
    BOOST_CHECK_EQUAL(map.size(), 1U);
    BOOST_CHECK_EQUAL(Count(map), 1);
    BOOST_CHECK_EQUAL(map.Search(key)->value, 2);
}

// Random inserts, updates, deletes and re-inserts of a small key pool, so that cells are reused
// and the table rehashes often; the map must always match a std::map.
BOOST_AUTO_TEST_CASE(random_against_std_map)
{
    uint256HashMap<int> map;
    map.Set(8);
    std::map<uint256, int> model;
    const std::vector<uint256> pool = Keys(48);
    for (int op = 0; op < 20000; op++) {
        const uint256& key = pool[InsecureRandRange(pool.size())];
        auto* found = map.Search(key);
        BOOST_REQUIRE_EQUAL(found != nullptr, model.count(key) == 1);
        if (found)
            BOOST_REQUIRE_EQUAL(found->value, model[key]);
        if (InsecureRandBool() && found) {
            map.MarkDel(found);
            model.erase(key);
        } else {
            map.Insert(key, op);
            model[key] = op;
        }
        BOOST_REQUIRE_EQUAL(map.size(), model.size());
        if (op % 97 == 0) {
            std::map<uint256, int> listed;
            for (auto* p = map.First(); p != nullptr; p = map.Next(p))
                BOOST_REQUIRE(listed.emplace(p->key, p->value).second); // no key twice
            BOOST_REQUIRE(listed == model);
        }
    }
}

BOOST_AUTO_TEST_SUITE_END()
