FROM ubuntu:22.04
LABEL description="This is a docker image for HOL4P4"
ARG DEBIAN_FRONTEND=noninteractive
ENV DEBCONF_NOWARNINGS="yes"
USER root

# First, get the repo
#RUN apt update
#RUN apt-get install -y build-essential git python3
#RUN git clone --depth 1 https://github.com/kth-step/HOL4P4.git
# Version without git
RUN mkdir /HOL4P4

COPY hol /HOL4P4/hol
COPY ott /HOL4P4/ott
COPY scripts /HOL4P4/scripts

# This lets us use the same installation scripts
RUN apt update && apt-get install -y -q sudo

# Then, just run the regular install script
RUN ./HOL4P4/scripts/install.sh

# Test compilation
RUN apt update && apt install -y \
    autoconf \
    automake \
    bison \
    build-essential \
    ccache \
    cmake \
    flex \
    git \
    g++ \
    iproute2 \
    libboost-dev \
    libboost-program-options-dev \
    libboost-thread-dev \
    libbsd-dev \
    libevent-dev \
    libgmp-dev \
    libgrpc++-dev \
    libgrpc-dev \
    libjsoncpp-dev \
    liblua5.3-dev \
    libnanomsg-dev \
    libpcap-dev \
    libpcap0.8-dev \
    libprotobuf-dev \
    libprotoc-dev \
    libreadline-dev \
    libssl-dev \
    libthrift-dev \
    libtool \
    libtool-bin \
    libxxhash-dev \
    lua5.3 \
    ninja-build \
    pkg-config \
    protobuf-compiler \
    protobuf-compiler-grpc \
    python3-dev \
    python3-pip \
    python3-six \
    python3-thrift \
    thrift-compiler \
    wget

RUN pip3 install meson pyelftools

RUN python3 -m pip install --upgrade pynng==0.9.0

RUN git clone https://github.com/numactl/numactl.git /tmp/numactl && \
    cd /tmp/numactl && \
    git checkout v2.0.19 && \
    ./autogen.sh && \
    ./configure && \
    make && \
    make install

RUN git clone git://dpdk.org/dpdk /tmp/dpdk && \
    cd /tmp/dpdk && \
    git checkout v26.03 && \
    meson setup build && \
    ninja -C build && \
    ninja -C build install && \
    ldconfig

RUN git clone https://github.com/p4lang/behavioral-model /tmp/behavioral-model && \
    cd /tmp/behavioral-model && \
    git checkout 1.15.2 && \
    sh ci/install-nanomsg.sh && \
    sh ci/install-thrift.sh && \
    ./autogen.sh && \
    ./configure --disable-logging-macros && \
    make && \
    make install

RUN git clone https://github.com/kth-step/swswitch-perf /swswitch-perf && \
    cd /swswitch-perf && \
    git checkout 78dfb87dc7e5de5e6ef464751ca02b0db8e612bd

RUN apt update && apt install -y \
    linux-tools-6.8.0-124-generic \
    pciutils

RUN git clone https://github.com/kth-step/Pktgen-DPDK.git /tmp/Pktgen-DPDK && \
    cd /tmp/Pktgen-DPDK && \
    git checkout for_hol4p4_26.03.0 && \
    make buildlua

COPY Makefile /HOL4P4/Makefile
RUN cd /HOL4P4/hol/cake_sem/programs/compilation && \
    ./setup_cake.sh

RUN PATH=$PATH:/HOL/bin:/root/.opam/4.13.1/bin && \
    cd /HOL4P4 && \
    make hol && \
    make hol/p4_from_json && \
    cd hol/symb_exec && \
    Holmake

RUN mkdir /swswitch-perf/programs
RUN cp /HOL4P4/hol/cake_sem/programs/port_swap.p4 /swswitch-perf/programs/port_swap.p4

RUN apt update && apt install -y iptables curl

RUN . /etc/lsb-release && \
    echo "deb http://download.opensuse.org/repositories/home:/p4lang/xUbuntu_${DISTRIB_RELEASE}/ /" \
    > /etc/apt/sources.list.d/home:p4lang.list && \
    curl -fsSL https://download.opensuse.org/repositories/home:p4lang/xUbuntu_${DISTRIB_RELEASE}/Release.key | gpg --dearmor | sudo tee /etc/apt/trusted.gpg.d/home_p4lang.gpg > /dev/null && \
    apt update && \
    apt install -y p4lang-p4c

RUN cd /swswitch-perf/programs && p4c --target bmv2 --arch v1model --std p4-16 port_swap.p4

RUN git clone https://github.com/CakeML/cakeml /cakeml && \
    cd cakeml && \
    git checkout vHOL-Trindemossen-2 && \
    PATH=$PATH:/HOL/bin Holmake

RUN cd /HOL4P4/hol/cake_sem/programs && \
    PATH=$PATH:/HOL/bin:/root/.opam/4.13.1/bin Holmake

RUN cd /HOL4P4/hol/cake_sem/programs && \
    ./build_cake.sh port_swap && \
    cp compilation/port_swap.cake /swswitch-perf/programs/port_swap.cake

WORKDIR /swswitch-perf
ENTRYPOINT ["/bin/bash", "-c", "bash setup_test_env.sh /tmp/dpdk && bash --login"]
