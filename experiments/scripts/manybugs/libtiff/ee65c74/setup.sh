project_name=libtiff
bug_id=ee65c74
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2006-03-03-eec4c06-ee65c74.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz libtiff-bug-2006-03-03-eec4c06-ee65c74.tar.gz
mv libtiff-bug-2006-03-03-eec4c06-ee65c74 src
cd src/libtiff

make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32
