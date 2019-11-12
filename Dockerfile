FROM ubuntu:18.04
MAINTAINER Danil Annenkov <http://dannenkov.me>

# Lean build flags
ENV CMAKE_FLAGS="-D CMAKE_BUILD_TYPE=RELEASE -D BOOST=OFF -D TCMALLOC=OFF -G Ninja"

# Set non-interactive mode
ARG DEBIAN_FRONTEND=noninteractive

ENV LANG C.UTF-8

# Install the required packages

RUN apt-get update && \
    apt-get install \
     nano \
     python \
     git \
     libgmp-dev \
     libmpfr-dev \
     emacs \
     cmake \
     liblua5.2.0 \
     lua5.2-0 \
     lua5.2-dev \
     gitg \
     ninja-build \
     valgrind \
     doxygen -y

# RUN update-alternatives --remove-all gcc

# RUN update-alternatives --remove-all g++

# RUN apt-get update
RUN apt-get install g++-4.8 -y
RUN apt-get upgrade -y && apt-get dist-upgrade -y

RUN update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 0

RUN g++ --version

# Download from the repository, build, clean up
RUN \
  git clone --depth 1 https://github.com/leanprover/lean2.git && \
  mkdir -p lean2/build && \
  (cd lean2/build; cmake $CMAKE_FLAGS ../src && ninja && ninja install) && \
  lean --version && \
  rm -rf lean

RUN mkdir /root/.emacs.d
ADD extra/init.el /root/.emacs.d
RUN ls ~/.emacs.d
RUN emacs --batch -l /root/.emacs.d/init.el

RUN mkdir /root/2ltt
ADD 2ltt /root/2ltt/

RUN cd ~/2ltt && linja

# This is just a convenience for running the container. It can be overridden.
ENTRYPOINT ["/bin/bash"]
