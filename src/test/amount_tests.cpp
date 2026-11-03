// Copyright (c) 2016-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <amount.h>
#include <policy/feerate.h>
#include <primitives/transaction.h>
#include <test/setup_common.h>

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(amount_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(MoneyRangeTest)
{
    BOOST_CHECK_EQUAL(MoneyRange(CAmount(-1)), false);
    BOOST_CHECK_EQUAL(MoneyRange(CAmount(0)), true);
    BOOST_CHECK_EQUAL(MoneyRange(CAmount(1)), true);
    BOOST_CHECK_EQUAL(MoneyRange(MAX_MONEY), true);
    BOOST_CHECK_EQUAL(MoneyRange(MAX_MONEY + CAmount(1)), false);
}

BOOST_AUTO_TEST_CASE(GetFeeTest)
{
    CFeeRate feeRate, altFeeRate;

    // emercoin: fees are flat, CFeeRate::GetFee() ignores the rate and returns GetMinFee():
    // MIN_TX_FEE per started 10 KiB
    for (const CAmount rate : {CAmount(0), CAmount(1000), CAmount(-1000), CAmount(123)}) {
        feeRate = CFeeRate(rate);
        BOOST_CHECK_EQUAL(feeRate.GetFee(0), MIN_TX_FEE);
        BOOST_CHECK_EQUAL(feeRate.GetFee(1), MIN_TX_FEE);
        BOOST_CHECK_EQUAL(feeRate.GetFee(10239), MIN_TX_FEE);
        BOOST_CHECK_EQUAL(feeRate.GetFee(10240), 2 * MIN_TX_FEE);
        BOOST_CHECK_EQUAL(feeRate.GetFee(1e5), 10 * MIN_TX_FEE);
    }
    BOOST_CHECK_EQUAL(GetMinFee(std::numeric_limits<size_t>::max()), MAX_MONEY);

    // check alternate constructor
    feeRate = CFeeRate(1000);
    altFeeRate = CFeeRate(feeRate);
    BOOST_CHECK_EQUAL(feeRate.GetFee(100), altFeeRate.GetFee(100));

    // Check full constructor
    BOOST_CHECK(CFeeRate(CAmount(-1), 0) == CFeeRate(0));
    BOOST_CHECK(CFeeRate(CAmount(0), 0) == CFeeRate(0));
    BOOST_CHECK(CFeeRate(CAmount(1), 0) == CFeeRate(0));
    // default value
    BOOST_CHECK(CFeeRate(CAmount(-1), 1000) == CFeeRate(-1));
    BOOST_CHECK(CFeeRate(CAmount(0), 1000) == CFeeRate(0));
    BOOST_CHECK(CFeeRate(CAmount(1), 1000) == CFeeRate(1));
    // lost precision (can only resolve satoshis per kB)
    BOOST_CHECK(CFeeRate(CAmount(1), 1001) == CFeeRate(0));
    BOOST_CHECK(CFeeRate(CAmount(2), 1001) == CFeeRate(1));
    // some more integer checks
    BOOST_CHECK(CFeeRate(CAmount(26), 789) == CFeeRate(32));
    BOOST_CHECK(CFeeRate(CAmount(27), 789) == CFeeRate(34));
    // Maximum size in bytes, should not crash
    CFeeRate(MAX_MONEY, std::numeric_limits<size_t>::max() >> 1).GetFeePerK();
}

BOOST_AUTO_TEST_CASE(BinaryOperatorTest)
{
    CFeeRate a, b;
    a = CFeeRate(1);
    b = CFeeRate(2);
    BOOST_CHECK(a < b);
    BOOST_CHECK(b > a);
    BOOST_CHECK(a == a);
    BOOST_CHECK(a <= b);
    BOOST_CHECK(a <= a);
    BOOST_CHECK(b >= a);
    BOOST_CHECK(b >= b);
    // a should be 0.00000002 BTC/kB now
    a += a;
    BOOST_CHECK(a == b);
}

BOOST_AUTO_TEST_CASE(ToStringTest)
{
    CFeeRate feeRate;
    feeRate = CFeeRate(1);
    BOOST_CHECK_EQUAL(feeRate.ToString(), "0.000001 EMC/kB");
}

BOOST_AUTO_TEST_SUITE_END()
