FROM --platform=linux/amd64 ubuntu:24.04

COPY . /Triton

RUN apt update && \
    apt upgrade -y

# libboost >= 1.83
# libpython >= 3.12
# llvm >= 16.0
RUN DEBIAN_FRONTEND="noninteractive" \
    apt install -y --no-install-suggests --no-install-recommends \
        build-essential \
        clang \
        curl \
        git \
        libboost-all-dev \
        libgmp-dev \
        libpython3-dev \
        libpython3-stdlib \
        llvm-16 \
        llvm-16-dev \
        ninja-build \
        pkg-config \
        python3-pip \
        python3-venv \
        tar && \
    apt clean

ENV VIRTUAL_ENV=/Triton-venv
RUN python3 -m venv $VIRTUAL_ENV
ENV PATH="$VIRTUAL_ENV/bin:$PATH"
RUN . $VIRTUAL_ENV/bin/activate

# cmake >= 3.20
# libz3 >= 4.13.0
RUN python3 -m pip install --upgrade pip && \
    python3 -m pip install \
        cmake \
        lief \
        meson \
        setuptools \
        unicorn \
        z3-solver

# libcapstone >= 5.0.x
RUN echo "[+] Download, build and install Capstone" && \
    cd /tmp && \
    curl -s -o capstone-5.0.1.tar.gz -L https://github.com/aquynh/capstone/archive/5.0.1.tar.gz && \
    tar xf capstone-5.0.1.tar.gz && \
    cd ./capstone-5.0.1 && \
    CAPSTONE_ARCHS="arm aarch64 riscv x86" ./make.sh && \
    make install

# libbitwuzla >= 0.4.0
RUN echo "[+] Download, build and install Bitwuzla" && \
    cd /tmp && \
    git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    python3 ./configure.py --shared && \
    cd build && \
    meson install

RUN echo "[+] Build and install Triton" && \
    Z3_PATH=$(python -c "import site; print(f'{site.getsitepackages()[0]}/z3')") && \
    # Triton (LLVM for lifting; z3 or bitwuzla as SMT solver)
    cd /Triton && \
    mkdir /tmp/triton-build && \
    cd /tmp/triton-build && \
    cmake -GNinja \
        -DLLVM_INTERFACE=ON \
        -DCMAKE_PREFIX_PATH=$(llvm-config-16 --prefix) \
        -DZ3_INTERFACE=ON \
        -DBITWUZLA_INTERFACE=ON \
        /Triton && \
        ninja install 

RUN echo "[+] Check Triton build" && \
    echo export "PATH=$VIRTUAL_ENV/bin:$PATH" >> /etc/bash.bashrc && \
    # Print z3 version.
    python3 -c "import z3; print('Z3 version:', z3.get_version_string())" && \
    # Next command fails if Triton has no z3 or bitwuzla support.
    python3 -c "from triton import *; ctx=TritonContext(ARCH.X86_64); ctx.setSolver(SOLVER.Z3); ctx.setSolver(SOLVER.BITWUZLA);"

ENTRYPOINT ["/bin/bash"]
