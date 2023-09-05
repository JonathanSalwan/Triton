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

RUN python3.10 -m pip install meson
ENV PATH=/opt/_internal/cpython-3.10.13/bin:$PATH
ENV DEPENDENCIES_DIR=/tmp/triton-dependencies
ENV SOURCE_DIR=/src

# Create directory for dependencies.
RUN mkdir -p $DEPENDENCIES_DIR

# Download, build and install GMP.
RUN echo "[+] Download, build and install GMP" && \
    cd $DEPENDENCIES_DIR  && \
    wget -q https://ftp.gnu.org/gnu/gmp/gmp-6.2.1.tar.xz && \
    tar -xf gmp-6.2.1.tar.xz && \
    cd gmp-6.2.1 && \
    ./configure --enable-cxx && \
    make && \
    make install

# Download, build and install Bitwuzla.
RUN echo "[+] Download, build and install Bitwuzla" && \
    cd $DEPENDENCIES_DIR && \
    git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    git checkout -b 0.1.0 0.1.0 && \
    CC=clang CXX=clang++ PATH=$PATH:/opt/_internal/cpython-3.10.12/bin python3.10 ./configure.py --shared --prefix $(pwd)/install && \
    cd build && \
    PATH=$PATH:/opt/_internal/cpython-3.10.12/bin ninja install

# Download Z3.
RUN echo "[+] Download Z3" && \
cd $DEPENDENCIES_DIR && \
wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.8.17/z3-4.8.17-x64-glibc-2.31.zip && \
unzip z3-4.8.17-x64-glibc-2.31.zip

# Download, build and install Capstone.
RUN echo "[+] Download, build and install Capstone" && \
    cd $DEPENDENCIES_DIR && \
    wget -q https://github.com/aquynh/capstone/archive/4.0.2.tar.gz -O capstone-4.0.2.tar.gz && \
    tar -xf capstone-4.0.2.tar.gz && \
    cd capstone-4.0.2 && \
    bash ./make.sh && \
    sudo make install

# Download LLVM.
RUN echo "[+] Download LLVM" && \
    cd $DEPENDENCIES_DIR && \
    wget -q https://github.com/llvm/llvm-project/releases/download/llvmorg-12.0.1/clang+llvm-12.0.1-x86_64-linux-gnu-ubuntu-16.04.tar.xz && \
    tar -xf clang+llvm-12.0.1-x86_64-linux-gnu-ubuntu-16.04.tar.xz
