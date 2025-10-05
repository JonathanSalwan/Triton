ARG BASE_IMG=quay.io/pypa/manylinux_2_34_x86_64

FROM $BASE_IMG

RUN yum install -y \
        cmake \
        clang \
        git \
        less \
        ninja-build \
        sudo \
        wget

# LLVM dependencies.
RUN yum install -y \
        libxml2-devel \
        libzstd-devel \
        ncurses-devel

RUN python3.10 -m pip install meson

ENV DEPENDENCIES_DIR=/tmp/triton-dependencies
ENV SOURCE_DIR=/src

# Create directory for dependencies.
RUN mkdir -p $DEPENDENCIES_DIR

# Download, build and install Bitwuzla.
RUN echo "[+] Download, build and install Bitwuzla" && \
    cd $DEPENDENCIES_DIR && \
    git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    export PY310_PATH=$(python3.10 -c 'import sys, os; print(os.path.dirname(sys.executable))') && \
    CC=clang CXX=clang++ PATH=$PATH:$PY310_PATH python3.10 ./configure.py --shared --prefix $(pwd)/install && \
    cd build && \
    PATH=$PATH:$PY310_PATH ninja -j $(nproc) install

# Download Z3.
RUN echo "[+] Download Z3" && \
    cd $DEPENDENCIES_DIR && \
    wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip && \
    unzip -q z3-4.12.2-x64-glibc-2.31.zip

# Download, build and install Capstone.
RUN echo "[+] Download, build and install Capstone" && \
    cd $DEPENDENCIES_DIR && \
    wget -q https://github.com/capstone-engine/capstone/archive/refs/tags/5.0.3.tar.gz -O capstone-5.0.3.tar.gz && \
    tar xf capstone-5.0.3.tar.gz && \
    cd ./capstone-5.0.3 && \
    CAPSTONE_ARCHS="arm aarch64 riscv x86" ./make.sh && \
    sudo make install
