project_name=libtiff
bug_id=2e42d63
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/libtiff-bug-2009-02-05-764dbba-2e42d63.tar
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
#wget $download_url
cp $current_dir/libtiff-bug-2009-02-05-764dbba-2e42d63.tar .
tar xf libtiff-bug-2009-02-05-764dbba-2e42d63.tar
mv libtiff-bug-2009-02-05-764dbba-2e42d63 src
rm libtiff-bug-2009-02-05-764dbba-2e42d63.tar
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
cp $current_dir/tiffcrop.c ./tools/tiffcrop.c
make distclean
chown -R root $dir_name

## Compile libtiff.
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared
sed -i '978 s/./\t&/' test/Makefile
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32

cd $dir_name

## fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/libtiff-bug-2009-02-05-764dbba-2e42d63#/data/manybugs/libtiff/2e42d63#g" test.sh
sed -i "s#/data/manybugs/libtiff/2e42d63/src/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i "s#cd libtiff#cd src#g" test.sh

cd src

## Prepare for KLEE
# Fix fabs calls (not supported by KLEE).
sed -i 's/fabs/fabs_cpr/g' libtiff/tif_luv.c
sed -i 's/fabs/fabs_cpr/g' tools/tiff2ps.c
#sed -i 's/fabs_cpr/fabs/g' libtiff/tif_luv.c
#sed -i 's/fabs_cpr/fabs/g' tools/tiff2ps.c
make CC=$CPR_CC CXX=$CPR_CXX -j32

cd $dir_name

## Instrument driver and libtiff
sed -i '125i // KLEE' src/tools/tiffcrop.c
sed -i '126i #include <klee/klee.h>' src/tools/tiffcrop.c
sed -i '127i #ifndef CPR_OUTPUT' src/tools/tiffcrop.c
sed -i '128i #define CPR_OUTPUT(id, typestr, value) value' src/tools/tiffcrop.c
sed -i '129i #endif' src/tools/tiffcrop.c
#
sed -i '4256i \\tif (__cpr_choice("4256", "bool", (int[]){image->xres, image->yres, crop->res_unit}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0) &&' src/tools/tiffcrop.c
sed -i '4257d' src/tools/tiffcrop.c
#
sed -i '4386i \\t\t\treturn (-2);' src/tools/tiffcrop.c
sed -i '4387d' src/tools/tiffcrop.c
sed -i '4393i \\t\t\treturn (-3);' src/tools/tiffcrop.c
sed -i '4394d' src/tools/tiffcrop.c
sed -i '4493i \\t\treturn (-4);' src/tools/tiffcrop.c
sed -i '4494d' src/tools/tiffcrop.c
sed -i '4502i \\t\treturn (-5);' src/tools/tiffcrop.c
sed -i '4503d' src/tools/tiffcrop.c
#
sed -i '4546i \\t\tint tmp_res = computeInputPixelOffsets(crop, image, &offsets);' src/tools/tiffcrop.c
sed -i '4547i \\t\tklee_print_expr("tmp_res=", tmp_res);' src/tools/tiffcrop.c
sed -i '4548i \\t\tklee_print_expr("crop->res_unit=", crop->res_unit);' src/tools/tiffcrop.c
sed -i '4549i \\t\tklee_print_expr("obs=", (tmp_res != -1 || crop->res_unit != RESUNIT_NONE));' src/tools/tiffcrop.c
sed -i '4550i \\t\tCPR_OUTPUT("obs", "i32", (tmp_res != -1 || crop->res_unit != RESUNIT_NONE));' src/tools/tiffcrop.c
sed -i '4551i \\t\tklee_assert(tmp_res != -1 || crop->res_unit != RESUNIT_NONE);' src/tools/tiffcrop.c
sed -i '4552i \\t\tif (tmp_res)' src/tools/tiffcrop.c
sed -i '4553d' src/tools/tiffcrop.c

## Compile instrumentation and test driver.
cd src
make CXX=$CPR_CXX CC=$CPR_CC CFLAGS="-lcpr_proxy -L/CPR/lib -L/klee/build/lib  -lkleeRuntest -I/klee/source/include -g -O0" -j32
cd tools
extract-bc tiffcrop

### Copy remaining files to run CPR.
cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp test-input $dir_name
cp -rf components $dir_name
cp -rf test-input-files $dir_name
cp -rf test-expected-output $dir_name
#cp -rf seed-dir $dir_name

#### Test with KLEE
##cd /data/manybugs/libtiff/865f7b2/src/tools
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libcpr_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/test-input-files/22-44-54-64-74-fail-palette-1c-1b.tiff test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libcpr_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/test-input-files/13-14-15-16-17-22-43-53-63-73-fail-miniswhite-1c-1b.tiff test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libcpr_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/seed-dir/2-pass-long_test.tiff test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libcpr_runtime.bca --write-smt2s tiffcp.bc /data/manybugs/libtiff/865f7b2/seed-dir/22-40-50-60-70-pass-minisblack-1c-16b.tiff test.tif
##
#cd /data/manybugs/libtiff/865f7b2/test-input-files
#gen-bout --sym-file "/data/manybugs/libtiff/865f7b2/test-input-files/22-44-54-64-74-fail-palette-1c-1b.tiff"
#cd /data/manybugs/libtiff/865f7b2/src/tools
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libcpr_runtime.bca --write-smt2s --seed-out=/data/manybugs/libtiff/865f7b2/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching tiffcp.bc A --sym-files 1 3312 test.tif
#klee --posix-runtime --libc=uclibc --link-llvm-lib=/CPR/lib/libcpr_runtime.bca --write-smt2s --seed-out=/data/manybugs/libtiff/865f7b2/test-input-files/file.bout --allow-seed-extension --resolve-path --named-seed-matching tiffcp.bc A --sym-files 1 3312 test.tif
##
