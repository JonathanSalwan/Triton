#! /usr/bin/env bash

# This file is used for building the docker image necessary to build
# triton-library with the manylinux tag. It is used by the Build Python
# Package Github workflow but can also be used locally.

set -ex

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

docker build \
    --build-arg BASE_IMG=quay.io/pypa/manylinux_2_34_x86_64 \
    --tag build-triton-linux-x86_64 \
    $SCRIPT_DIR
