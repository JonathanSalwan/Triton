FROM ubuntu:20.04
LABEL maintainer="David Manouchehri"

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get dist-upgrade -y && \
    apt-get install -y git cmake build-essential clang ca-certificates curl \
    unzip libboost-dev python3-dev python3-pip && apt-get clean

# get and install the latest z3 relesae
RUN cd /tmp && \
    curl -o z3.tgz -L  https://github.com/Z3Prover/z3/archive/z3-4.8.9.tar.gz && \
    tar zxf z3.tgz && cd z3-z3-4.8.9 && \
    mkdir build && cd build && CC=clang CXX=clang++ cmake .. && make \
    && make install && cd /tmp && rm -rf /tmp/z3-z3-4.8.9

# Install capstone
RUN cd /tmp && \
    curl -o cap.tgz -L https://github.com/aquynh/capstone/archive/4.0.2.tar.gz && \
    tar xvf cap.tgz && cd capstone-4.0.2/ && ./make.sh && make install && cd /tmp && \
    rm -rf /tmp/capstone-4.0.2

# Install Triton
RUN cd /opt && git clone https://github.com/JonathanSalwan/Triton.git && \
    cd Triton && mkdir build && cd build && cmake .. && make install

# Configure libTriton path for Python
RUN echo export PYTHONPATH=\"/usr/lib/python\$\(python3 -c \'import sys\; print\(\".\".join\(map\(str, sys.version_info[:2]\)\)\)\'\)/site-packages:\$PYTHONPATH\" >> /etc/bash.bashrc

ENTRYPOINT /bin/bash
