FROM ubuntu:22.04
LABEL description="Docker image for the PolyGram artifact (FMCAD 2026)"

ARG DEBIAN_FRONTEND=noninteractive
ENV DEBCONF_NOWARNINGS="yes"

USER root

# ---- 1. System dependencies --------------------------------------------------------------------------------------------------------
RUN apt-get update && apt-get install -y -q \
    build-essential git python3 file \
    zlib1g-dev libbz2-dev liblzma-dev wget sudo \
    opam make nano && \
    rm -rf /var/lib/apt/lists/*

# ---- 2. Copy the full project into the image ----------------------------------------------------------------------
# (.dockerignore excludes the prebuilt cakeml/ folder)
COPY . /HOL4P4

# ---- 3. Install Poly/ML 5.9.2 --------------------------------------------------------------------------------------------------
WORKDIR /HOL4P4
RUN wget https://github.com/polyml/polyml/archive/refs/tags/v5.9.2.tar.gz && \
    tar -xvf v5.9.2.tar.gz && \
    cd polyml-5.9.2 && \
    ./configure --prefix=/usr && \
    make && \
    make install && \
    cd .. && rm -rf polyml-5.9.2 v5.9.2.tar.gz

# ---- 4. Install HOL4 Trindemossen-2 --------------------------------------------------------------------------------------
WORKDIR /HOL4P4
RUN git clone https://github.com/HOL-Theorem-Prover/HOL.git && \
    cd HOL && \
    git checkout trindemossen-2 && \
    sed -i 's/CFLAGS    = -Wall -ffloat-store -fno-strict-aliasing.*/& -std=c++14/g' \
        src/HolSat/sat_solvers/minisat/Makefile && \
    sed -i 's/g++ -O3 Proof.o File.o zc2hs.cpp -o zc2hs.*/& -std=c++14/g' \
        src/HolSat/sat_solvers/zc2hs/Makefile && \
    poly < tools/smart-configure.sml && \
    bin/build

ENV PATH="/HOL4P4/HOL/bin:$PATH"

# ---- 5. Install OPAM + OCaml ------------------------------------------------------------------------------------------------------
RUN opam init --disable-sandboxing -y && \
    eval $(opam env)

# ---- 6. Clone and build CakeML (vHOL-Trindemossen-2) fresh inside Docker --------------
WORKDIR /HOL4P4
RUN git clone https://github.com/CakeML/cakeml.git && \
    cd cakeml && \
    git checkout vHOL-Trindemossen-2 && \
    eval $(opam env) && \
    cd misc && Holmake && cd .. && \
    cd basis && Holmake && cd .. && \
    cd translator && Holmake && cd .. && \
    cd unverified/sexpr-bootstrap && Holmake && cd ../..

# ---- 7. Make preprocessing scripts executable ------------------------------------------------------------------
WORKDIR /HOL4P4
RUN chmod +x hol/polygram/policy_test_cases*/prepp.sh && \
    chmod +x hol/polygram/reviewers_test_here/prepp.sh


# ---- 8. Set working directory for reviewers ------------------------------------------------------------------------
WORKDIR /HOL4P4

# ---- 9. Pre-build everything so reviewers can inspect immediately ----------------------------
RUN make hol
RUN make polygram
RUN eval $(opam env) && make cake
RUN eval $(opam env) && make test

ENTRYPOINT ["/bin/bash", "--login"]