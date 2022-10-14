FROM rshariffdeen/ubuntu:18.04
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>
ARG DEBIAN_FRONTEND=noninteractive

COPY --from=rshariffdeen/z3:4.8.4 /opt/z3/ /z3/
COPY --from=rshariffdeen/llvm:6.0.0 /opt/llvm-6/ /opt/llvm-6/
COPY --from=rshariffdeen/klee:latest /klee/ /klee
COPY --from=rshariffdeen/klee:latest /klee-uclibc /klee-uclibc

ENV PATH "/opt/llvm-6/bin:/klee/build/bin:${PATH}"
ENV LLVM_COMPILER=clang

RUN add-apt-repository -y ppa:pypy/ppa
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y  --no-install-recommends --force-yes \
    bear \
    file \
    gfortran \
    python3 \
    python3-dev \
    python3-pip \
    python3-setuptools

RUN python3 -m pip install --upgrade pip
RUN python3 -m pip --disable-pip-version-check --no-cache-dir install \
    cython \
    funcy \
    numpy \
    pylint \
    pysmt \
    setuptools \
    six \
    sympy \
    wllvm


ENV PATH "/home/user/.local/bin:${PATH}"
RUN pysmt-install --z3 --confirm-agreement
RUN ln -s /z3/lib/libz3.so /usr/lib/
ARG CACHEBUST=1
RUN git clone https://github.com/rshariffdeen/CPR.git /CPR
WORKDIR /CPR
RUN cd lib && KLEE_INCLUDE_PATH=/klee/source/include make
ENV DEBIAN_FRONTEND=dialog
ENV CPR_CC=/CPR/tools/cpr-cc
ENV CPR_CXX=/CPR/tools/cpr-cxx
RUN cd /klee/build/lib; ar rcs libkleeRuntest.a libkleeRuntest.so.1.0
RUN python3 setup.py build_ext --inplace
ENV PATH "/CPR/bin:${PATH}"
RUN cpr --help; exit 0
