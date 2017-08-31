/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file type_system_test.h
 *
 * Tests souffle's type system operations.
 *
 ***********************************************************************/

#include "GraphUtils.h"
#include "Util.h"
#include "test.h"

namespace souffle {

namespace test {

TEST(Graph, Basic) {
    Graph<int> g;

    EXPECT_FALSE(g.exists(1));
    EXPECT_FALSE(g.exists(2));
    EXPECT_FALSE(g.exists(3));

    EXPECT_FALSE(g.exists(1, 2));
    EXPECT_FALSE(g.exists(1, 3));
    EXPECT_FALSE(g.exists(2, 3));

    EXPECT_FALSE(g.reaches(1, 1));
    EXPECT_FALSE(g.reaches(1, 2));
    EXPECT_FALSE(g.reaches(1, 3));
    EXPECT_FALSE(g.reaches(2, 1));
    EXPECT_FALSE(g.reaches(2, 2));
    EXPECT_FALSE(g.reaches(2, 3));
    EXPECT_FALSE(g.reaches(3, 1));
    EXPECT_FALSE(g.reaches(3, 2));
    EXPECT_FALSE(g.reaches(3, 3));

    g.insert(1, 2);

    EXPECT_TRUE(g.exists(1));
    EXPECT_TRUE(g.exists(2));
    EXPECT_FALSE(g.exists(3));

    EXPECT_TRUE(g.exists(1, 2));
    EXPECT_FALSE(g.exists(1, 3));
    EXPECT_FALSE(g.exists(2, 3));

    EXPECT_FALSE(g.reaches(1, 1));
    EXPECT_TRUE(g.reaches(1, 2));
    EXPECT_FALSE(g.reaches(1, 3));
    EXPECT_FALSE(g.reaches(2, 1));
    EXPECT_FALSE(g.reaches(2, 2));
    EXPECT_FALSE(g.reaches(2, 3));
    EXPECT_FALSE(g.reaches(3, 1));
    EXPECT_FALSE(g.reaches(3, 2));
    EXPECT_FALSE(g.reaches(3, 3));

    g.insert(2, 3);

    EXPECT_TRUE(g.exists(1));
    EXPECT_TRUE(g.exists(2));
    EXPECT_TRUE(g.exists(3));

    EXPECT_TRUE(g.exists(1, 2));
    EXPECT_FALSE(g.exists(1, 3));
    EXPECT_TRUE(g.exists(2, 3));

    EXPECT_FALSE(g.reaches(1, 1));
    EXPECT_TRUE(g.reaches(1, 2));
    EXPECT_TRUE(g.reaches(1, 3));
    EXPECT_FALSE(g.reaches(2, 1));
    EXPECT_FALSE(g.reaches(2, 2));
    EXPECT_TRUE(g.reaches(2, 3));
    EXPECT_FALSE(g.reaches(3, 1));
    EXPECT_FALSE(g.reaches(3, 2));
    EXPECT_FALSE(g.reaches(3, 3));

    g.insert(3, 1);

    EXPECT_TRUE(g.exists(1));
    EXPECT_TRUE(g.exists(2));
    EXPECT_TRUE(g.exists(3));

    EXPECT_TRUE(g.exists(1, 2));
    EXPECT_FALSE(g.exists(1, 3));
    EXPECT_TRUE(g.exists(2, 3));

    EXPECT_TRUE(g.reaches(1, 1));
    EXPECT_TRUE(g.reaches(1, 2));
    EXPECT_TRUE(g.reaches(1, 3));
    EXPECT_TRUE(g.reaches(2, 1));
    EXPECT_TRUE(g.reaches(2, 2));
    EXPECT_TRUE(g.reaches(2, 3));
    EXPECT_TRUE(g.reaches(3, 1));
    EXPECT_TRUE(g.reaches(3, 2));
    EXPECT_TRUE(g.reaches(3, 3));

    EXPECT_EQ("{1->2,2->3,3->1}", toString(g));
}

}  // end namespace test
}  // end namespace souffle
