FROM --platform=linux/amd64 ubuntu:20.04
ARG DEBIAN_FRONTEND=noninteractive

COPY . /Triton

# libboost >= 1.68
# libpython >= 3.6
# llvm >= 12
# cmake >= 3.20
RUN apt update && apt upgrade -y && apt install -y build-essential clang curl git libboost-all-dev libgmp-dev libpython3-dev libpython3-stdlib llvm-12 llvm-12-dev python3-pip tar ninja-build pkg-config && apt-get clean && pip install --upgrade pip && pip3 install Cython lief cmake meson

# libcapstone >= 4.0.x
RUN cd /tmp && \
    curl -o cap.tgz -L https://github.com/aquynh/capstone/archive/4.0.2.tar.gz && \
    tar xvf cap.tgz && cd capstone-4.0.2/ && ./make.sh && make install && rm -rf /tmp/cap* \
    && ln -s /usr/lib/libcapstone.so.4 /usr/lib/x86_64-linux-gnu/libcapstone.so

# libbitwuzla >= 0.2.0
RUN cd /tmp && \
    git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    git checkout -b 0.2.0 0.2.0 && \
    python3 ./configure.py --shared && \
    cd build && \
    ninja install && \
    ldconfig

# To test pre-releases 'pip install' the corresponding .whl from https://github.com/Z3Prover/z3/releases/tag/Nightly
# libz3 >= 4.6.0
RUN pip3 install z3-solver==4.8.14

RUN PYV=`python3 -c "import platform;print(platform.python_version()[:3])"` && \
    # Triton (LLVM for lifting; z3 or bitwuzla as SMT solver)
    cd /Triton && mkdir /tmp/triton-build && cd /tmp/triton-build && cmake -DLLVM_INTERFACE=ON -DCMAKE_PREFIX_PATH=$(/usr/lib/llvm-12/bin/llvm-config --prefix) -DZ3_INTERFACE=ON -DZ3_INCLUDE_DIRS=/usr/local/lib/python$PYV/dist-packages/z3/include/ -DZ3_LIBRARIES=/usr/local/lib/python$PYV/dist-packages/z3/lib/libz3.so -DBITWUZLA_INTERFACE=ON  -DBITWUZLA_INCLUDE_DIRS=/usr/local/include -DBITWUZLA_LIBRARIES=/usr/local/lib/x86_64-linux-gnu/libbitwuzla.so /Triton && make -j$(nproc) && make install

RUN PYV=`python3 -c "import platform;print(platform.python_version()[:3])"` && \
    PYP="/usr/lib/python$PYV/site-packages" && \
    echo export PYTHONPATH="$PYP:\$PYTHONPATH" >> /etc/bash.bashrc && \
    python3 -c "import z3; print('Z3 version:', z3.get_version_string())" && \
    # Next command fails if Triton has no z3 or bitwuzla support
    PYTHONPATH="$PYP" python3 -c "from triton import *; ctx=TritonContext(ARCH.X86_64); ctx.setSolver(SOLVER.Z3); ctx.setSolver(SOLVER.BITWUZLA);"

# Dependencies required for testing
RUN pip install unicorn==2.0.0 lief

ENTRYPOINT /bin/bash
