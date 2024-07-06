#!/bin/bash
set -e

truncate -s 0 aflcc_cfg.bin && AFL_LLVM_CFG_FILE=aflcc_cfg.bin AFL_DONT_OPTIMIZE=1 ./afl-cc/afl-clang-cfg -fsanitize=dataflow -mllvm -dfsan-conditional-callbacks=true -fsanitize=fuzzer fuzz.c -o fuzz_dfsan
truncate -s 0 libafl_cfg.bin && AFL_LLVM_CFG_FILE=libafl_cfg.bin ./target/debug/libafl_cc --libafl fuzz_lafl.c -o fuzz_lafl
AFL_OLD_FORKSERVER=1 AFL_DEBUG=1 ./fuzz_lafl -c libafl_cfg.bin -d ./fuzz_dfsan -i corpus/ -o OUT |& tee run.log
