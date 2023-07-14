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
