project_name=gzip
bug_id=f17cbd13a1
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar.gz
current_dir=$PWD
#wget $download_url
mkdir -p $dir_name
cd $dir_name
cp $current_dir/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar .
tar xf gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar
mv gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1 src
rm gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1.tar
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

cp $dir_name/diffs/gzip.c-a1d3d4019d $dir_name/src/gzip.c

# Compile gzip.
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0'
CC=wllvm CXX=wllvm++ make CFLAGS="-g -O0 -static" -j32

cd $dir_name

## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/gzip-bug-2009-09-26-a1d3d4019d-f17cbd13a1#/data/manybugs/gzip/f17cbd13a1#g" test.sh
sed -i "s#/data/manybugs/gzip/f17cbd13a1/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd gzip#cd src#g" test.sh

cd $dir_name

## Instrument driver and libtiff
sed -i '73i // KLEE' src/gzip.c
sed -i '74i #include <klee/klee.h>' src/gzip.c
sed -i '75i #ifndef TRIDENT_OUTPUT' src/gzip.c
sed -i '76i #define TRIDENT_OUTPUT(id, typestr, value) value' src/gzip.c
sed -i '77i #endif' src/gzip.c
#
sed -i '658i \\t\tklee_print_expr("(before) ifd=", ifd);' src/gzip.c
sed -i '659i \\t\tifd = __trident_choice("659", "i32", (int[]){ifd, part_nb, to_stdout}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0);' src/gzip.c
sed -i '660i \\t\tklee_print_expr("obs=", ifd);' src/gzip.c
sed -i '661i \\t\tTRIDENT_OUTPUT("obs", "i32", ifd);' src/gzip.c
sed -i '662i \\t\tklee_assert(ifd == 0);' src/gzip.c

## Compile instrumentation and test driver.
cd src
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/CPR/lib -L/klee/build/lib  -lkleeRuntest -I/klee/source/include -g -O0" -j32
extract-bc gzip

## Copy remaining files to run CPR.
cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp test-input $dir_name
cp -rf components $dir_name
cp -rf test-input-files $dir_name
#cp -rf seed-dir $dir_name

# ### Test with KLEE
#
# gzip -dc in - in < in > out
#
# cd /data/manybugs/gzip/f17cbd13a1/src/
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s gzip.bc -dc /data/manybugs/gzip/f17cbd13a1/test-input-files/in - /data/manybugs/gzip/f17cbd13a1/test-input-files/in < /data/manybugs/gzip/f17cbd13a1/test-input-files/in > out
#
# cd /data/manybugs/gzip/f17cbd13a1/test-input-files
# gen-bout --sym-file "/data/manybugs/gzip/f17cbd13a1/test-input-files/in"
# cd /data/manybugs/gzip/f17cbd13a1/src
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc A --sym-files 1 3312 - A --sym-files 1 3312  < A --sym-files 1 3312
#
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc A --sym-files 1 3312 - B --sym-files 1 3312  < C --sym-files 1 3312
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc A --sym-files 1 3312 - /data/manybugs/gzip/f17cbd13a1/test-input-files/in < /data/manybugs/gzip/f17cbd13a1/test-input-files/in
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc /data/manybugs/gzip/f17cbd13a1/test-input-files/in - A --sym-files 1 3312 < /data/manybugs/gzip/f17cbd13a1/test-input-files/in
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc A --sym-files 1 3312 - B --sym-files 1 3312 < /data/manybugs/gzip/f17cbd13a1/test-input-files/in
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc /data/manybugs/gzip/f17cbd13a1/test-input-files/in - /data/manybugs/gzip/f17cbd13a1/test-input-files/in < A --sym-files 1 3312
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc A --sym-files 1 3312 - < /data/manybugs/gzip/f17cbd13a1/test-input-files/in
#
# klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libtrident_runtime.bca --write-smt2s --seed-out=/data/manybugs/gzip/f17cbd13a1/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching gzip.bc -dc A --sym-files 1 3312 - A < /data/manybugs/gzip/f17cbd13a1/test-input-files/in
#
#
# ./gzip -dc in - < in
