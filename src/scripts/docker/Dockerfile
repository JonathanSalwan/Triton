ARG BASE_IMG

FROM $BASE_IMG

# Download and install basic dependencies.
RUN apt-get update

RUN DEBIAN_FRONTEND="noninteractive" \
    apt-get install -y  --no-install-suggests --no-install-recommends \
        build-essential \
        ca-certificates \
        cmake \
        git-core \
        less \
        sudo \
        wget

# Add new user.
RUN adduser --uid 1000 --disabled-password --gecos '' docker
RUN adduser docker sudo
RUN echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers

# USER docker
