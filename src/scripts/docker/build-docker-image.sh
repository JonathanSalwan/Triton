#! /usr/bin/env bash

set -ex

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

docker build \
    --build-arg BASE_IMG=quay.io/pypa/manylinux_2_24_x86_64 \
    --tag build-triton-linux-x86_64 \
    $SCRIPT_DIR
