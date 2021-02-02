project_name=libtiff
bug_id=207c78a
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2006-02-23-b2ce5d8-207c78a.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz libtiff-bug-2006-02-23-b2ce5d8-207c78a.tar.gz
mv libtiff-bug-2006-02-23-b2ce5d8-207c78a src
rm libtiff-bug-2006-02-23-b2ce5d8-207c78a.tar.gz
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
mv libtiff src
cd $dir_name/src
cp $current_dir/tif_dirwrite.c ./libtiff/tif_dirwrite.c
make distclean
chown -R root $dir_name

# Fix fabs calls (not supported by KLEE).
#sed -i 's/fabs/fabs_trident/g' src/libtiff/tif_luv.c
#sed -i 's/fabs/fabs_trident/g' src/tools/tiff2ps.c

#CC=wllvm CXX=wllvm++ make -j32
#cd src
#make CC=$TRIDENT_CC -j32

# Compile libtiff.
make clean
CC=wllvm CXX=wllvm++ ./configure --enable-static --disable-shared
CC=wllvm CXX=wllvm++ make -j32
#
#cd ./test
#CC=wllvm CXX=wllvm++ make short_tag.log
#CC=wllvm CXX=wllvm++ make long_tag.log
#make CC=$TRIDENT_CC -j32 short_tag.log
#make CC=$TRIDENT_CC -j32 long_tag.log

#test
#%

#CC=wllvm CXX=wllvm++ ./configure CFLAGS='-m32' CXXFLAGS='-m32' LDFLAGS='-m32' --enable-static --disable-shared
#CC=wllvm CXX=wllvm++ make -j32

cd $dir_name

#sudo apt-get update
#sudo apt-get install -y --force-yes psmisc
#sudo apt-get install -y --force-yes zlib1g-dev
#sudo apt-get install -y --force-yes gcc-multilib
#sudo apt-get install -y --force-yes g++-multilib
#    sudo apt-get clean && \
#    sudo apt-get autoremove && \
#    sudo rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/libtiff-bug-2006-02-23-b2ce5d8-207c78a#/data/manybugs/libtiff/207c78a#g" test.sh
sed -i "s#/data/manybugs/libtiff/207c78a/src/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd libtiff#cd src#g" test.sh




#sed -i '118d;221d' libtiff/tif_jpeg.c
#sed -i '153d;2429d' libtiff/tif_ojpeg.c
#git add libtiff/tif_ojpeg.c libtiff/tif_jpeg.c
#git commit -m 'remove longjmp calls'


#make CFLAGS="-ltrident_proxy -L/concolic-repair/lib -g" -j32
#sed -i '358i }' tools/gif2tiff.c
#sed -i '353i { TRIDENT_OUTPUT("obs", "i32", count);\n if (count < 0) klee_abort();\n' tools/gif2tiff.c
#sed -i '352d' tools/gif2tiff.c
#sed -i '352i while ((count = getc(infile)) &&  count <= 255 && (__trident_choice("L65", "bool", (int[]){count, status}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) )' tools/gif2tiff.c
#sed -i '43i #ifndef TRIDENT_OUTPUT\n#define TRIDENT_OUTPUT(id, typestr, value) value\n#endif\n' tools/gif2tiff.c
#git add tools/gif2tiff.c
#git commit -m "instrument trident"

#cd $current_dir
#cp repair.conf $dir_name
#cp spec.smt2 $dir_name
#cp t1.smt2 $dir_name
#cp -rf components $dir_name
#cp -rf tests $dir_name
