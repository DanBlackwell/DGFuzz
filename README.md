# PrescientFuzz

PrescientFuzz is a fuzzer with improved exploration abilities. To achieve this, it takes in a copy of the fuzzing target's control flow graph and uses this to predict which inputs are worth fuzzing.

A full write-up is available [here](https://arxiv.org/pdf/2404.18887).

## Building and Running a Target Program

WARNING: Right now, the build is fiddly and only works for some versions of LLVM.

First you need to build the fuzzer; this is modified from LibAFL's `fuzzbench` fuzzer (to try and get the max performance). First let's go ahead and build that:

```
cd fuzzers/fuzzbench
cargo build --release
```

Now, building your target requires you to use the compiler wrapper we just built, so:

```
export CC=$(pwd)/target/release/libafl_cc
export CXX=$(pwd)/target/release/libafl_cxx
```

You need to specify where the control flow graph will be output (note that this is in a propietary binary format currently, see `libafl_cc/src/SanitizerCoverage.cpp::dumpCFGtoFile` to see it):

```
export AFL_LLVM_CFG_FILE=${YOUR_TARGET_DIR}/afl_cfg.bin
```

Finally, you should be able to build your target with the standard procedure (Make or equivalent). Then running it is a case of supplying the input seeds directory (`-i`), output directory (`-o`) and control flow graph file path (`-c`). For example:

```
mkdir seeds && echo "TEST" > seeds/seed
./my_built_target_binary -i seeds -o OUT -c $AFL_LLVM_CFG_FILE
```

For more info about LibAFL that this is modified from, see [here](LibAFL_README.md).
