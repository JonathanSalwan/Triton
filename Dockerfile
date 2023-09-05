FROM --platform=linux/amd64 ubuntu:20.04
ARG DEBIAN_FRONTEND=noninteractive

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

# libbitwuzla >= 0.1.0
RUN cd /tmp && \
    git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    git checkout -b 0.1.0 0.1.0 && \
    python3 ./configure.py --shared && \
    cd build && \
    ninja install && \
    ldconfig

# libz3 >= 4.6.0
RUN cd /tmp && \
    curl -o z3.tgz -L https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.8.14.tar.gz && \
    tar zxf z3.tgz && cd z3-z3-4.8.14 && mkdir build && cd build && \
    CC=clang CXX=clang++ cmake -DCMAKE_BUILD_TYPE=Release .. && make -j4 && make install && \
    pip3 install z3-solver && rm -rf /tmp/z3*

# Triton (LLVM for lifting; z3 or bitwuzla as SMT solver)
RUN git clone https://github.com/JonathanSalwan/Triton && cd Triton && mkdir build && cd build && cmake -DLLVM_INTERFACE=ON -DCMAKE_PREFIX_PATH=$(/usr/lib/llvm-12/bin/llvm-config --prefix) -DZ3_INTERFACE=ON -DBITWUZLA_INTERFACE=ON  -DBITWUZLA_INCLUDE_DIRS=/usr/local/include -DBITWUZLA_LIBRARIES=/usr/local/lib/x86_64-linux-gnu/libbitwuzla.so .. && make -j4 && make install

RUN PYV=`python3 -c "import platform;print(platform.python_version()[:3])"` && \
    PYP="/usr/lib/python$PYV/site-packages" && \
    echo export PYTHONPATH="$PYP:\$PYTHONPATH" >> /etc/bash.bashrc && \
    python3 -c "import z3; print('Z3 version:', z3.get_version_string())" && \
    # Next command fails if Triton has no z3 or bitwuzla support
    PYTHONPATH="$PYP" python3 -c "from triton import *; ctx=TritonContext(ARCH.X86_64); ctx.setSolver(SOLVER.Z3); ctx.setSolver(SOLVER.BITWUZLA);"

ENTRYPOINT /bin/bash
