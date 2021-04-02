FROM rshariffdeen/cpr:16.04
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>
ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get upgrade -y && apt-get autoremove -y

# install experiment dependencies
RUN apt-get update && apt-get install -y  \
    autopoint \
    automake \
    bison \
    flex \
    gettext \
    gperf \
    libass-dev \
    libfreetype6 \
    libfreetype6-dev \
    libjpeg-dev \
    libtool \
    libxml2-dev \
    liblzma-dev \
    nasm \
    pkg-config \
    texinfo \
    yasm \
    xutils-dev \
    libpciaccess-dev \
    libpython-dev \
    libpython3-dev \
    libx11-dev \
    libxcb-xfixes0-dev \
    libxcb1-dev \
    libxcb-shm0-dev \
    libsdl1.2-dev  \
    libvdpau-dev \
    libnuma-dev

RUN mkdir /experiments
ADD extractfix /experiments
ADD manybugs /experiments
ADD svcomp /experiments
ADD driver.py /experiments
ADD meta-data /experiments
RUN git config --global user.email "rshariffdeen@gmail.com"
RUN git config --global user.name "Ridwan"
WORKDIR /CPR

