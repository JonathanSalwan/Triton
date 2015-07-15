# This Dockerfile can be used to get Triton working on any docker host
# The Triton framework uses Intel PinTool and therefore needs to be able
# to inject itself inside the process you want to analyze.
# Depending on your host's kernel, you will have to allow this by configuring it.
# If your operating system forbid parent injection you will see the following
# error:
#       E: Attach to pid XX failed. 
#       E:   The Operating System configuration prevents Pin from using the default (parent) injection mode.
#       E:   To resolve this, either execute the following (as root):
#       E:   $ echo 0 > /proc/sys/kernel/yama/ptrace_scope
#       E:   Or use the "-injection child" option.
#       E:   For more information, regarding child injection, see Injection section in the Pin User Manual.
#       E: 
#
# "Echoing" 0 into /proc/sys/kernel/yama/ptrace_scope won't be enough and you will have to run the
# container into privileged mode (--privileged). However, using it isn't really secure.
# Here is the best way to run the container I have found so far:
#
# 
#       $ docker run -i -t --cap-add=SYS_PTRACE --security-opt apparmor:unconfined triton
#
#
#                                                               p-col.


FROM ubuntu:14.04

RUN apt-get update && apt-get install -y wget cmake git python2.7-dev g++ libboost-filesystem-dev
RUN mkdir /Triton

# Install Z3
WORKDIR /tmp
RUN git clone https://github.com/Z3Prover/z3.git

RUN ln -s /usr/bin/python2.7 /usr/bin/python
RUN cd /tmp/z3/ && /bin/bash ./configure && cd build && make && make install


WORKDIR /Triton/


# Install Intel Pintool
RUN wget http://software.intel.com/sites/landingpage/pintool/downloads/pin-2.14-71313-gcc.4.4.7-linux.tar.gz
RUN tar -xf pin-2.14-71313-gcc.4.4.7-linux.tar.gz

WORKDIR /Triton/pin-2.14-71313-gcc.4.4.7-linux/source/tools/

# Install Triton
RUN git clone https://github.com/JonathanSalwan/Triton.git

WORKDIR /Triton/pin-2.14-71313-gcc.4.4.7-linux/source/tools/Triton

RUN mkdir build && cd build && cmake .. && make

CMD ["./triton", "examples/callback_after.py","samples/ir_test_suite/ir"]