project_name=php
bug_id=426f31e790
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/php-bug-2011-02-05-c50b3d7add-426f31e790.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz php-bug-2011-02-05-c50b3d7add-426f31e790.tar.gz
mv php-bug-2011-02-05-c50b3d7add-426f31e790 src
cd src/php

make clean
CC=wllvm CXX=wllvm++  ./configure \
  --enable-cli \
  --disable-dom \
  --disable-libxml  \
  --disable-xml \
  --disable-simplexml \
  --disable-xmlreader  \
  --disable-xmlwriter  \
  --disable-pear  \
  --disable-phar \
  --disable-inline-optimization  \
  --without-pcre-dir  \
  --disable-fileinfo \
  --disable-shared

CC=clang CXX=clang++ make  -j32

sed -i 's/fabs/fabs_trident/g' ./ext/gd/libgd/gd.c
sed -i 's/fabs/fabs_trident/g' ./ext/gd/libgd/gd_rotate.c
sed -i 's/fabs/fabs_trident/g' ./ext/sqlite3/libsqlite/sqlite3.c
sed -i 's/fabs/fabs_trident/g' ./ext/standard/math.c

make CXX=clang++ CC=clang LDFLAGS="-ltrident_proxy -L/CPR/lib -L/klee/build/lib -lkleeRuntest" CFLAGS="-g -O0 -static"  sapi/cli/php
