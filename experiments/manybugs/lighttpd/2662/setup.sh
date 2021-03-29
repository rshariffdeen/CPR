project_name=lighttpd
bug_id=2662
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/lighttpd-bug-2661-2662.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz lighttpd-bug-2661-2662.tar.gz
mv lighttpd-bug-2661-2662 src
cd src/lighttpd

make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0'
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32