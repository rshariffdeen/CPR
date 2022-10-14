FROM rshariffdeen/ubuntu:18.04
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


COPY --from=rshariffdeen/z3:4.8.4 /opt/z3/ /opt/z3/
COPY --from=rshariffdeen/llvm:6.0.0 /opt/llvm-6/ /opt/llvm-6/
COPY --from=rshariffdeen/klee:latest /klee/ /klee
COPY --from=rshariffdeen/klee:latest /klee-uclibc /klee-uclibc

ENV PATH "/opt/llvm-6/bin:/klee/build/bin:${PATH}"
ENV LLVM_COMPILER=clang
RUN add-apt-repository -y ppa:deadsnakes/ppa
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y  --no-install-recommends --force-yes \
    bear \
    python3 \
    python3-dev \
    python3-pip \
    python3-setuptools

RUN python3 -m pip install --upgrade pip
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install setuptools
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install pylint
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install cython==3.0a7
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install pysmt==0.9.1.dev132
RUN pysmt-install --z3 --confirm-agreement
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install funcy
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install six
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install numpy
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install wllvm; return 0;

## Install PyPy JITC
RUN add-apt-repository -y ppa:pypy/ppa
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y  --no-install-recommends --force-yes \
    gfortran \
    pypy3 \
    pypy3-dev

RUN pypy3 -m easy_install cython==3.0a7
RUN pypy3 -m easy_install setuptools
RUN pypy3 -m easy_install pysmt==0.9.1.dev132
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
ENV CPR_CC=/CPR/tools/cpr-cc
ENV CPR_CXX=/CPR/tools/cpr-cxx
RUN cd /klee/build/lib; ar rcs libkleeRuntest.a libkleeRuntest.so.1.0
RUN pypy3 setup.py build_ext --inplace
ENV PATH "/CPR/bin:${PATH}"
RUN cpr --help
