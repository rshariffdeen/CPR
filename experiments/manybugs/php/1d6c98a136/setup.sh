project_name=php
bug_id=1d6c98a136
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/php-bug-2011-01-29-147382033a-5bb0a44e06.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz php-bug-2011-01-29-147382033a-5bb0a44e06.tar.gz
mv php-bug-2011-01-29-147382033a-5bb0a44e06 src
cd src/php

make clean
CC=wllvm CXX=wllvm++ ./configure  \
                    --enable-static \
                    --disable-shared \
                    --disable-inline-optimization \
                    --disable-xmlwriter \
                    --disable-xmlreader  \
                    --enable-cli  \
                    --disable-dom \
                    --disable-xml  \
                    --disable-pear \
                    --disable-simplexml  \
                    --disable-phar \
                    --disable-inline-optimization \
                    --disable-fileinfo \
                    --disable-libxml   \
                    --without-pear  \
                    --without-pcre-dir



CC=wllvm CXX=wllvm++ LDFLAGS="-L/CPR/lib -lcpr_proxy" CFLAGS="-g -O0" CXXFLAGS="-g -O0"  make  -j32

CC=wllvm CXX=wllvm++ CFLAGS="-no-asm -Dasm=error -D__asm__=error" CXXFLAGS="-no-asm -Dasm=error -D__asm__=error" make -j32

