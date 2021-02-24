project_name=gzip
bug_id=884ef6d16c
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/gzip-bug-2010-02-19-3eb6091d69-884ef6d16c.tar.gz
current_dir=$PWD
wget $download_url
mkdir -p $dir_name
cd $dir_name
cp $current_dir/gzip-bug-2010-02-19-3eb6091d69-884ef6d16c.tar.gz .
tar xfz gzip-bug-2010-02-19-3eb6091d69-884ef6d16c.tar.gz
mv gzip-bug-2010-02-19-3eb6091d69-884ef6d16c src
rm gzip-bug-2010-02-19-3eb6091d69-884ef6d16c.tar.gz
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
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0'
CXX=$TRIDENT_CXX CC=$TRIDENT_CC make CFLAGS="-g -O0 -static" -j32

cd $dir_name/src
cp $dir_name/diffs/gzip.c-3eb6091d69 $dir_name/src/gzip.c
#Instrument driver and libtiff
sed -i '168i #endif' gzip.c
sed -i '168i #define TRIDENT_OUTPUT(id, typestr, value) value' gzip.c
sed -i '168i #ifndef TRIDENT_OUTPUT' gzip.c
sed -i '551i if ((z_len == 0 && __trident_choice("L1634", "bool", (int[]){z_len, MAX_SUFFIX, decompress}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0)) || z_len > MAX_SUFFIX) { ' gzip.c
sed -i '552d' gzip.c
sed -i '556i \\tklee_assert(z_len > 0);' gzip.c
sed -i '556i \\tTRIDENT_OUTPUT("obs", "i32", z_len);' gzip.c


# Compile instrumentation and test driver.
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC CFLAGS="-ltrident_proxy -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include -g -O0" -j32


# Copy remaining files to run CPR.
cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp test-input-file $dir_name
cp -rf components $dir_name
cp -rf test-expected-output $dir_name
cp -rf test-input-files $dir_name
cd $dir_name
