// Copyright (c) 2011-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.
//

#include <netaddress.h>
#include <noui.h>
#include <test/setup_common.h>
#include <timedata.h>
#include <warnings.h>

#include <limits>
#include <string>

#include <boost/test/unit_test.hpp>

BOOST_FIXTURE_TEST_SUITE(timedata_tests, BasicTestingSetup)

BOOST_AUTO_TEST_CASE(util_MedianFilter)
{
    CMedianFilter<int> filter(5, 15);

    BOOST_CHECK_EQUAL(filter.median(), 15);

    filter.input(20); // [15 20]
    BOOST_CHECK_EQUAL(filter.median(), 17);

    filter.input(30); // [15 20 30]
    BOOST_CHECK_EQUAL(filter.median(), 20);

    filter.input(3); // [3 15 20 30]
    BOOST_CHECK_EQUAL(filter.median(), 17);

    filter.input(7); // [3 7 15 20 30]
    BOOST_CHECK_EQUAL(filter.median(), 15);

    filter.input(18); // [3 7 18 20 30]
    BOOST_CHECK_EQUAL(filter.median(), 18);

    filter.input(0); // [0 3 7 18 30]
    BOOST_CHECK_EQUAL(filter.median(), 7);
}

BOOST_AUTO_TEST_CASE(time_offset_sample)
{
    const int64_t now = 1700000000;
    const int64_t limit = std::numeric_limits<int64_t>::max() / 4;
    BOOST_CHECK_EQUAL(TimeOffsetSample(now + 4200, now), 4200);
    BOOST_CHECK_EQUAL(TimeOffsetSample(now - 4200, now), -4200);
    BOOST_CHECK_EQUAL(TimeOffsetSample(0, now), -now);
    BOOST_CHECK_EQUAL(TimeOffsetSample(std::numeric_limits<int64_t>::max(), now), limit - now);
    BOOST_CHECK_EQUAL(TimeOffsetSample(std::numeric_limits<int64_t>::min(), now), -limit);
    BOOST_CHECK_EQUAL(TimeOffsetSample(std::numeric_limits<int64_t>::min(), std::numeric_limits<int64_t>::max()), -limit);
    BOOST_CHECK_EQUAL(TimeOffsetSample(std::numeric_limits<int64_t>::max(), std::numeric_limits<int64_t>::min()), limit);
}

static void MultiAddTimeData(int n, int64_t offset)
{
    static int cnt = 0;
    for (int i = 0; i < n; ++i) {
        CNetAddr addr;
        addr.SetInternal(std::to_string(++cnt));
        AddTimeData(addr, offset);
    }
}


BOOST_AUTO_TEST_CASE(addtimedata)
{
    BOOST_CHECK_EQUAL(GetTimeOffset(), 0);

    //Part 1: Add large offsets to test a warning message that our clock may be wrong.
    MultiAddTimeData(3, DEFAULT_MAX_TIME_ADJUSTMENT + 1);
    // Filter size is 1 + 3 = 4: It is always initialized with a single element (offset 0)

    noui_suppress();
    MultiAddTimeData(1, DEFAULT_MAX_TIME_ADJUSTMENT + 1); //filter size 5
    noui_reconnect();

    BOOST_CHECK(GetWarnings("gui").find("clock is wrong") != std::string::npos);

    // nTimeOffset is not changed if the median of offsets exceeds DEFAULT_MAX_TIME_ADJUSTMENT
    BOOST_CHECK_EQUAL(GetTimeOffset(), 0);

    // Part 2: Test positive and negative medians by adding more offsets
    MultiAddTimeData(4, 100); // filter size 9
    BOOST_CHECK_EQUAL(GetTimeOffset(), 100);
    MultiAddTimeData(10, -100); //filter size 19
    BOOST_CHECK_EQUAL(GetTimeOffset(), -100);

    // Part 3: Test behaviour when filter has reached maximum number of offsets
    const int MAX_SAMPLES = 200;
    int nfill = (MAX_SAMPLES - 3 - 19) / 2; //89
    MultiAddTimeData(nfill, 100);
    MultiAddTimeData(nfill, -100); //filter size MAX_SAMPLES - 3
    BOOST_CHECK_EQUAL(GetTimeOffset(), -100);

    MultiAddTimeData(2, 100);
    //filter size MAX_SAMPLES -1, median is the initial 0 offset
    //since we added same number of positive/negative offsets

    BOOST_CHECK_EQUAL(GetTimeOffset(), 0);

    // emercoin: unlike Bitcoin (#4521), even filter sizes update nTimeOffset too, with the mean of
    // the two middle values; samples stop at MAX_SAMPLES peers.
    MultiAddTimeData(1, 100); // filter size MAX_SAMPLES: [-100 x99, 0, 100 x96, big x4]
    BOOST_CHECK_EQUAL(GetTimeOffset(), 50);
    MultiAddTimeData(1, -100); // the initial 0 drops out: [-100 x100, 100 x96, big x4]
    BOOST_CHECK_EQUAL(GetTimeOffset(), 0);
    MultiAddTimeData(5, 100); // MAX_SAMPLES peers seen: ignored
    BOOST_CHECK_EQUAL(GetTimeOffset(), 0);

    // We want this test to end with nTimeOffset==0, otherwise subsequent tests of the suite will fail.
}

BOOST_AUTO_TEST_SUITE_END()
