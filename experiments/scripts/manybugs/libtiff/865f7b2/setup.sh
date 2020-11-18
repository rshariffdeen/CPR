project_name=libtiff
bug_id=865f7b2
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2007-11-02-371336d-865f7b2.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz libtiff-bug-2007-11-02-371336d-865f7b2.tar.gz
mv libtiff-bug-2007-11-02-371336d-865f7b2 src
cd src/libtiff

make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32
