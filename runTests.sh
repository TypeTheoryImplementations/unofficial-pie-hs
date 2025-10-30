#!/usr/bin/env bash

cabal run unofficial-pie-hs --                                  \
    tests/pie/bookTests/OneNeqZero.pie                          \
    tests/pie/bookTests/OnePlusOneEqualsTwo.pie                 \
    tests/pie/customTests/testsThatShouldPass/TestProgram1.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram2.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram3.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram4.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram5.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram6.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram7.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram8.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram9.pie  \
    tests/pie/customTests/testsThatShouldPass/TestProgram10.pie \
    tests/pie/customTests/testsThatShouldPass/TestProgram11.pie \
    tests/pie/customTests/testsThatShouldPass/TestProgram12.pie

cabal run unofficial-pie-hs --                                  \
    tests/pie/customTests/testsThatShouldFail/TestProgram1.pie  \
    tests/pie/customTests/testsThatShouldFail/TestProgram2.pie  \
    tests/pie/customTests/testsThatShouldFail/TestProgram3.pie  \
    tests/pie/customTests/testsThatShouldFail/TestProgram4.pie  \
    tests/pie/customTests/testsThatShouldFail/TestProgram5.pie  \
    tests/pie/customTests/testsThatShouldFail/TestProgram6.pie
