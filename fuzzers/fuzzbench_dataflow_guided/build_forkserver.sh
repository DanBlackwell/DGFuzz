#!/bin/bash
set -e

cd afl-cc
  make
  cd utils/aflpp_driver
    make
  cd ../../
cd ../

cargo build

truncate -s 0 aflcc_cfg.bin && AFL_LLVM_CFG_FILE=aflcc_cfg.bin ./afl-cc/afl-clang-dgfuzz -fsanitize=fuzzer fuzz.c -o fuzz_dfsan
truncate -s 0 libafl_cfg.bin && AFL_LLVM_CFG_FILE=libafl_cfg.bin ./target/debug/libafl_cc --libafl fuzz.c -o fuzz_lafl
AFL_DEBUG=1 ./fuzz_lafl -c libafl_cfg.bin -d ./fuzz_dfsan -i corpus/ -o OUT |& tee run.log
