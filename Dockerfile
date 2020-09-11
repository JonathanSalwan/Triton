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


# Install pintool
RUN cd /opt && curl -o pin.tgz -L http://software.intel.com/sites/landingpage/pintool/downloads/pin-2.14-71313-gcc.4.4.7-linux.tar.gz && tar zxf pin.tgz

# now install Triton
# uncomment below to pull form git
# RUN cd /opt/pin-2.14-71313-gcc.4.4.7-linux/source/tools/ && git clone https://github.com/JonathanSalwan/Triton.git && \
#     cd Triton && mkdir build && cd build && cmake -G "Unix Makefiles" -DPINTOOL=on -DKERNEL4=on .. && \
#     make install && cd .. && python setup.py install
RUN cd /opt/pin-2.14-71313-gcc.4.4.7-linux/source/tools/ && \
   curl -o master.zip -L https://github.com/JonathanSalwan/Triton/archive/master.zip && unzip master.zip && cd Triton-master/ && mkdir build && cd build && \
   cmake -G "Unix Makefiles" -DPINTOOL=on -DKERNEL4=on .. && make install && cd ..

ENTRYPOINT /bin/bash
