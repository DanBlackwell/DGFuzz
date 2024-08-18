FROM ubuntu:24.04


RUN apt-get update && \
    apt-get install -y curl llvm-16-dev clang-16 && \
    cp /usr/bin/clang-16 /usr/bin/clang && \
    cp /usr/bin/clang++-16 /usr/bin/clang++

ENV LLVM_CONFIG llvm-config-16

# Uninstall old Rust & Install the latest one.
RUN if which rustup; then rustup self uninstall -y; fi && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > /rustup.sh && \
    sh /rustup.sh -y && \
    /root/.cargo/bin/rustup toolchain install nightly && \
    rm /rustup.sh

RUN apt-get update && \
    apt-get install -y \
        build-essential \
        cargo && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y wget libstdc++5 libtool-bin automake flex bison \
        libglib2.0-dev libpixman-1-dev python3-setuptools unzip \
        apt-utils apt-transport-https ca-certificates joe curl nlohmann-json3-dev && \
    PATH="/root/.cargo/bin/:$PATH" cargo install cargo-make

COPY ./ /dgfuzz

# RUN cd /dgfuzz && \
#     unset CFLAGS CXXFLAGS && \
#     export CC=clang AFL_NO_X86 && \
#     cd ./fuzzers/fuzzbench_dataflow_guided && \
#     PATH="/root/.cargo/bin/:$PATH" cargo +nightly build --profile release-fuzzbench --features no_link_main
# Compile DGFuzz.
RUN cd /dgfuzz && \
    export CC=clang-16 CXX=clang++-16 LLVM_CONFIG=llvm-config-16 && \
    unset CFLAGS CXXFLAGS && \
    cd ./fuzzers/fuzzbench_dataflow_guided && \
    PATH="/root/.cargo/bin/:$PATH" cargo +nightly build --profile release-fuzzbench --features no_link_main

# Auxiliary weak references.
RUN cd /dgfuzz/fuzzers/fuzzbench_dataflow_guided && \
    clang-16 -c stub_rt.c && \
    ar r /stub_rt.a stub_rt.o

# install AFL++ dependencies
RUN apt-get update && \
    apt-get install -y \
        build-essential \
        python3-dev \
        python3-setuptools \
        automake \
        cmake \
        git \
        flex \
        bison \
        libglib2.0-dev \
        libpixman-1-dev \
        cargo \
        libgtk-3-dev \
        # for QEMU mode
        ninja-build \
        gcc-$(gcc --version|head -n1|sed 's/\..*//'|sed 's/.* //')-plugin-dev \
        libstdc++-$(gcc --version|head -n1|sed 's/\..*//'|sed 's/.* //')-dev

# compile afl-clang-dgfuzz
RUN cd /dgfuzz/fuzzers/fuzzbench_dataflow_guided/afl-cc && \
    unset CFLAGS CXXFLAGS && \
    export CC=clang-16 AFL_NO_X86=1 LLVM_CONFIG=llvm-config-16 && \
    PYTHON_INCLUDE=/ make && \
    cd utils/aflpp_driver/ && \
    PYTHON_INCLUDE=/ make && \
    cp ./libAFLDriver.a /
