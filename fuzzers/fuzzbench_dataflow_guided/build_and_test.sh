#!/usr/bin/bash
set -e

clang -c stub_rt.c
CC=clang cargo build
touch afl_cfg.bin
truncate -s 0 afl_cfg.bin
FUZZER_LIB=$PWD/stub_rt.a $PWD/target/debug/libafl_cc -c test_dfsan.c -fPIC -fsanitize=dataflow -dfsan-conditional-callbacks=true -o harness-dfsan.o
AFL_LLVM_CFG_FILE=afl_cfg.bin $PWD/target/debug/libafl_cc -c test_dfsan.c --libafl-no-link -o harness.o
AFL_LLVM_CFG_FILE=afl_cfg.bin $PWD/target/debug/libafl_cc -fsanitize=dataflow harness-dfsan.o harness.o --libafl -o dfsan_test
./dfsan_test -c afl_cfg.bin -i corpus -o OUT
