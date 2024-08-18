#! /usr/bin/env bash
set -e

SCRIPT_DIR="$(cd -P -- "$(dirname -- "$0")" && pwd -P)"
FUZZER_DIR=../fuzzers/fuzzbench_dataflow_guided

# build the fuzzer
cd $FUZZER_DIR
CC=clang CXX=clang++ cargo build
cd afl-cc
set +e
# make clean
CC=clang CXX=clang++ make
cd utils/aflpp_driver 
# make clean
CC=clang CXX=clang++ make
cp libAFLDriver.a $SCRIPT_DIR/
set -e
cd $SCRIPT_DIR

# create / empty the module offsets file
export AFL_LLVM_MODULE_OFFSETS_FILE=./module_offsets.json
touch $AFL_LLVM_MODULE_OFFSETS_FILE
truncate -s 0 $AFL_LLVM_MODULE_OFFSETS_FILE

# create / empty the CFG file
export AFL_LLVM_CFG_FILE=./aflpp_cfg.bin
touch $AFL_LLVM_CFG_FILE
truncate -s 0 $AFL_LLVM_CFG_FILE

# build the DFSan binary
ls $FUZZER_DIR/afl-cc
CC=$FUZZER_DIR/afl-cc/afl-clang-dgfuzz
CFLAGS="-fsanitize=fuzzer"
export AFL_LLVM_FIRST_BUILD=1
rm -rf dfsan/*
mkdir -p dfsan
$CC $CFLAGS -c ifs.c -o ifs.o
$CC $CFLAGS -c switches.c -o switches.o
$CC $CFLAGS ifs.o switches.o main.c -o dfsan/run_main

# create / empty the CFG file
export AFL_LLVM_CFG_FILE=./libafl_cfg.bin
touch $AFL_LLVM_CFG_FILE
truncate -s 0 $AFL_LLVM_CFG_FILE

# build the normal binary (with fuzzer compiled in)
CC=$FUZZER_DIR/target/debug/libafl_cc
export -n AFL_LLVM_FIRST_BUILD
$CC $CFLAGS -c ifs.c -o ifs.o
$CC $CFLAGS -c switches.c -o switches.o
$CC $CFLAGS ifs.o switches.o main.c -o run_main