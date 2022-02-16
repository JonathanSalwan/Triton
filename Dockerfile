FROM ubuntu:20.04
ARG DEBIAN_FRONTEND=noninteractive

# libboost >= 1.68
# libpython >= 3.6
# llvm >= 12
RUN apt update && apt upgrade -y && apt install -y build-essential cmake clang curl git libboost-all-dev libgmp-dev libpython3-dev libpython3-stdlib llvm-12 llvm-12-dev python3-pip tar && apt-get clean && \ 
pip install --upgrade pip && pip3 install Cython

# libz3 >= 4.6.0
RUN cd /tmp && \
    curl -o z3.tgz -L https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.8.14.tar.gz && \
    tar zxf z3.tgz && cd z3-z3-4.8.14 && \
    mkdir build && cd build && CC=clang CXX=clang++ cmake .. && make \
    && make install && rm -rf /tmp/z3*

# libbitwuzla
RUN cd /tmp && \ 
    git clone https://github.com/bitwuzla/bitwuzla && cd bitwuzla && \ 
    ./contrib/setup-cadical.sh && ./contrib/setup-btor2tools.sh && ./contrib/setup-symfpu.sh && \
    ./configure.sh && cd build && make && rm -rf /tmp/bitwuzla

# libcapstone >= 4.0.x
RUN cd /tmp && \
    curl -o cap.tgz -L https://github.com/aquynh/capstone/archive/4.0.2.tar.gz && \
    tar xvf cap.tgz && cd capstone-4.0.2/ && ./make.sh && make install && rm -rf /tmp/cap* \
    && ln -s /usr/lib/libcapstone.so.4 /usr/lib/x86_64-linux-gnu/libcapstone.so

# Triton
RUN git clone https://github.com/JonathanSalwan/Triton && cd Triton && mkdir build && cd build && cmake .. && make -j3 && make install


RUN PYV=`python3 -c "import platform;print(platform.python_version()[:3])"` && PYP="/usr/lib/python$PYV/site-packages" && echo export PYTHONPATH="$PYP:\$PYTHONPATH" >> /etc/bash.bashrc && PYTHONPATH="$PYP" python3 -c "from triton import *"

ENTRYPOINT /bin/bash
