project_name=gzip
bug_id=f17cbd13a1
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar.gz
current_dir=$PWD
wget $download_url
mkdir -p $dir_name
cd $dir_name
cp $current_dir/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar.gz .
tar xfz gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar.gz
mv gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1 src
rm gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar.gz
mv src/* .
rm -rf src
rm -rf  coverage* \
        configuration-oracle \
        local-root \
        limit* \
        *.cache \
        *.debug.* \
        sanity \
        compile.pl \
        *~ \
        test \
        reconfigure \
        preprocessed \
        fixed-program.txt
mv bugged-program.txt manifest.txt
mv *.lines bug-info
mv fix-failures bug-info
mv gzip src
cd $dir_name/src
make distclean
chown -R root $dir_name

# Compile gzip.
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0'
CC=wllvm CXX=wllvm++ make CFLAGS="-g -O0 -static" -j32

# Run Test Suite
cd $dir_name/src/tests
make helin-segv.log
make help-version.log
make hufts.log
make mixed.log
make memcpy-abuse.log
make null-suffix-clobber.log
make stdin.log
make trailing-nul.log
make zdiff.log

