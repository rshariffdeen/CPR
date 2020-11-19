project_name=php
bug_id=c2fe893985
dir_name=$1/manybugs/$project_name/$bug_id
tag_id=php-bug-2011-03-26-3acdca4703-c2fe893985
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/${tag_id}.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz ${tag_id}.tar.gz
mv $tag_id src
cd src/php

make clean
CC=wllvm CXX=wllvm++ ./configure --enable-cli --disable-dom --disable-xml --disable-pear --disable-simplexml --disable-phar --disable-inline-optimization --disable-fileinfo
CC=wllvm CXX=wllvm++ make  -j32
CC=wllvm CXX=wllvm++ make sapi/cli/php -j32