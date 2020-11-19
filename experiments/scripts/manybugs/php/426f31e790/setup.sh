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
CC=wllvm CXX=wllvm++ ./configure --enable-cli --disable-dom --disable-xml --disable-pear --disable-simplexml --disable-phar --disable-inline-optimization --disable-fileinfo
CC=wllvm CXX=wllvm++ make  -j32
CC=wllvm CXX=wllvm++ make sapi/cli/php -j32