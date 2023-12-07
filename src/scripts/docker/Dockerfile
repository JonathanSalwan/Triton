ARG BASE_IMG

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

# Download, build and install GMP.
RUN echo "[+] Download, build and install GMP" && \
    cd $DEPENDENCIES_DIR  && \
    wget -q https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz -O gmp-6.3.0.tar.xz && \
    tar -xf gmp-6.3.0.tar.xz && \
    cd gmp-6.3.0 && \
    ./configure --enable-cxx && \
    make -j $(nproc) && \
    make install

# Download, build and install Bitwuzla.
RUN echo "[+] Download, build and install Bitwuzla" && \
    cd $DEPENDENCIES_DIR && \
    git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    git checkout -b 0.2.0 0.2.0 && \
    export PY310_PATH=$(dirname $(realpath -L $(which python3.10))) && \
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
    wget -q https://github.com/capstone-engine/capstone/archive/refs/tags/5.0.1.tar.gz -O capstone-5.0.1.tar.gz && \
    tar xf capstone-5.0.1.tar.gz && \
    cd ./capstone-5.0.1 && \
    ./make.sh && \
    sudo make install
