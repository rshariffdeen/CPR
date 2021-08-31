FROM ubuntu:18.04
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get upgrade -y && apt-get autoremove -y
RUN apt-get install -y build-essential \
                       curl \
                       cmake \
                       git \
                       libcap-dev \
                       libgoogle-perftools-dev \
                       libncurses5-dev \
                       libtcmalloc-minimal4 \
                       libssl-dev \
                       nano \
                       psmisc  \
                       python \
                       software-properties-common \
                       unzip \
                       vim \
                       wget \
                       zlib1g-dev

ENV LLVM_VERSION=6.0
RUN apt-get install -y clang-${LLVM_VERSION} \
                       llvm-${LLVM_VERSION} \
                       llvm-${LLVM_VERSION}-dev \
                       llvm-${LLVM_VERSION}-tools

ENV Z3_VERSION=4.8.4
WORKDIR /z3
RUN wget -qO- https://github.com/Z3Prover/z3/archive/z3-${Z3_VERSION}.tar.gz | tar xz --strip-components=1 && \
    python scripts/mk_make.py && \
    cd build && \
    make && \
    make install
ENV PATH=/usr/lib/llvm-${LLVM_VERSION}/bin/:${PATH}
ENV KLEE_UCLIBC_VERSION=klee_0_9_29
WORKDIR /klee-uclibc
RUN git clone https://github.com/klee/klee-uclibc.git . && \
    git checkout ${KLEE_UCLIBC_VERSION} && \
    CC=clang ./configure --make-llvm-lib && \
    make -j2
ENV KLEE_VERSION=2.0
WORKDIR /klee 
RUN git clone https://github.com/rshariffdeen/klee.git source; cd source; git checkout concolic
RUN mkdir build && \
    cd build && \
    cmake \
        -DENABLE_SOLVER_Z3=ON \
        -DENABLE_POSIX_RUNTIME=ON \
        -DENABLE_KLEE_UCLIBC=ON \
        -DKLEE_UCLIBC_PATH=/klee-uclibc \
        -DENABLE_UNIT_TESTS=OFF \
        -DENABLE_SYSTEM_TESTS=OFF \
            ../source && \
    make
ENV PATH=/klee/build/bin/:${PATH}
ENV LLVM_COMPILER=clang
RUN add-apt-repository -y ppa:deadsnakes/ppa
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y  --no-install-recommends --force-yes \
    bear \
    python3.7 \
    python3.7-dev \
    python3-pip \
    python3-setuptools

RUN python3.7 -m pip install --upgrade pip
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install setuptools
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install pylint
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install cython
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install pysmt
RUN pysmt-install --z3 --confirm-agreement
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install funcy
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install six
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install numpy
RUN python3.7 -m pip --disable-pip-version-check --no-cache-dir install wllvm; return 0;

## Install PyPy JITC
RUN add-apt-repository -y ppa:pypy/ppa
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y  --no-install-recommends --force-yes \
    gfortran \
    pypy3 \
    pypy3-dev

RUN pypy3 -m easy_install cython
RUN pypy3 -m easy_install setuptools
RUN pypy3 -m easy_install pysmt
RUN pysmt-install --z3 --confirm-agreement
RUN pypy3 -m easy_install funcy
RUN pypy3 -m easy_install six
RUN pypy3 -m easy_install numpy==1.19.1
RUN pypy3 -m easy_install wllvm

ARG CACHEBUST=1
RUN git clone https://github.com/rshariffdeen/CPR.git /CPR
WORKDIR /CPR
RUN cd lib && KLEE_INCLUDE_PATH=/klee/source/include make
ENV DEBIAN_FRONTEND=dialog
ENV TRIDENT_CC=/CPR/tools/trident-cc
ENV TRIDENT_CXX=/CPR/tools/trident-cxx
RUN cd /klee/build/lib; ar rcs libkleeRuntest.a libkleeRuntest.so.1.0
RUN pypy3 setup.py build_ext --inplace
RUN ln -s /CPR/bin/cpr /usr/bin/cpr
