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
COPY . /HOL4P4

# This lets us use the same installation scripts
RUN apt update && apt-get install -y -q sudo

# Then, just run the regular install script
RUN ./HOL4P4/scripts/install.sh
WORKDIR /HOL4P4/

# Test compilation
#RUN export PATH=$PATH:/HOL4P4/HOL/bin && opam exec -- make hol

ENTRYPOINT ["/bin/bash", "--login"]
