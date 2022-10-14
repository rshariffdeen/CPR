project_name=gmp
bug_id=14167
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/gmp-bug-14166-14167.tar.gz
current_dir=$PWD
wget $download_url
mkdir -p $dir_name
cd $dir_name
cp $current_dir/gmp-bug-14166-14167.tar.gz .
tar xfz gmp-bug-14166-14167.tar.gz
mv gmp-bug-14166-14167 src
rm gmp-bug-14166-14167.tar.gz
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
mv gmp src
cd $dir_name/src
make distclean
chown -R root $dir_name

# Compile gzip.
make clean
mkdir tests/mpbsd/
touch tests/mpbsd/Makefile.in
cp $current_dir/ltmain.sh ltmain.sh
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' configure.in
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile.am
./.bootstrap
CC=wllvm CXX=wllvm++ ./configure --disable-shared --enable-static --disable-fft --disable-mpbsd --disable-cxx --disable-fast-install --disable-minithres

CC=wllvm CXX=wllvm++ ./configure --disable-shared --disable-cxx --disable-fast-install --enable-static;
sed -i 's/no-dependencies ansi2knr/no-dependencies/g' Makefile;
make -e fib_table.h;make -e mp_bases.h;
CC=clang CXX=clang++ make CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" -j32


cp ../diffs/mpn/generic/powm.c-13420 mpn/generic/powm.c
sed -i '76i #include <klee/klee.h>' mpn/generic/powm.c
sed -i '213d' mpn/generic/powm.c
sed -i '213i b2p = ( __cpr_choice("L1634", "i32", (int[]){rp, tp, n}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0));' mpn/generic/powm.c
sed -i '228i klee_silent_exit(0);' mpn/generic/powm.c

sed -i '23i #include <klee/klee.h>' mpn/generic/add_n.c
sed -i '23i #endif' mpn/generic/add_n.c
sed -i '23i #define CPR_OUTPUT(id, typestr, value) value' mpn/generic/add_n.c
sed -i '23i #ifndef CPR_OUTPUT' mpn/generic/add_n.c
sed -i '45i klee_assert(vp - rp == 1 || up - rp == 1);' mpn/generic/add_n.c
sed -i '45i CPR_OUTPUT("obs", "i32", vp - rp == 1 || up - rp == 1);' mpn/generic/add_n.c

cp $current_dir/t-jac.c tests/mpz/t-jac.c
sed -i 's/wllvm++/\/CPR\/tools\/cpr-cxx/g' mpn/Makefile
sed -i 's/wllvm/\/CPR\/tools\/cpr-cc/g' mpn/Makefile
CC=$CPR_CC CXX=$CPR_CXX make CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" -j32
cd tests/mpz
sed -i 's/wllvm++/\/CPR\/tools\/cpr-cxx/g' Makefile
sed -i 's/wllvm/\/CPR\/tools\/cpr-cc/g' Makefile
CC=$CPR_CC CXX=$CPR_CXX make CFLAGS="-g -O0 -static -I/klee/source/include -L/klee/build/lib -lkleeRuntest" t-jac

cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cd $dir_name
