#! /usr/bin/env bash
set -e

CC=../fuzzers/fuzzbench_dataflow_guided/afl-cc/afl-clang-cfg
export AFL_LLVM_CFG_FILE=./aflpp_cfg.bin
export AFL_LLVM_MODULE_OFFSETS_FILE=./module_offsets.json
export AFL_LLVM_FIRST_BUILD=1
rm -rf dfsan/*
mkdir -p dfsan
$CC $CFLAGS -c ifs.c -o ifs.o
$CC $CFLAGS -c switches.c -o switches.o
$CC $CFLAGS main.c -o dfsan/run_main

CC=../fuzzers/fuzzbench_dataflow_guided/target/debug/libafl_cc
export AFL_LLVM_CFG_FILE=./libafl_cfg.bin
export -n AFL_LLVM_FIRST_BUILD
$CC $CFLAGS -c ifs.c -o ifs.o
$CC $CFLAGS -c switches.c -o switches.o
$CC $CFLAGS main.c -o run_main