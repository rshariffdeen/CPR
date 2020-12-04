project_name=lighttpd
bug_id=1914
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/lighttpd-bug-1913-1914.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz lighttpd-bug-1913-1914.tar.gz
mv lighttpd-bug-1913-1914 src
cd src/lighttpd

make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared --with-pcre=no
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32

#sed -i 's/fabs/fabs_trident/g' libtiff/tif_luv.c
#sed -i 's/fabs/fabs_trident/g' tools/tiff2ps.c
#git add  libtiff/tif_luv.c tools/tiff2ps.c
#git commit -m 'replace fabs with proxy function'
#make CC=$TRIDENT_CC -j32


sed -i '118d;221d' libtiff/tif_jpeg.c
sed -i '153d;2429d' libtiff/tif_ojpeg.c
git add libtiff/tif_ojpeg.c libtiff/tif_jpeg.c
git commit -m 'remove longjmp calls'


make CFLAGS="-ltrident_proxy -L/concolic-repair/lib -g" -j32
sed -i '358i }' tools/gif2tiff.c
sed -i '353i { TRIDENT_OUTPUT("obs", "i32", count);\n if (count < 0) klee_abort();\n' tools/gif2tiff.c
sed -i '352d' tools/gif2tiff.c
sed -i '352i while ((count = getc(infile)) &&  count <= 255 && (__trident_choice("L65", "bool", (int[]){count, status}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) )' tools/gif2tiff.c
sed -i '43i #ifndef TRIDENT_OUTPUT\n#define TRIDENT_OUTPUT(id, typestr, value) value\n#endif\n' tools/gif2tiff.c
git add tools/gif2tiff.c
git commit -m "instrument trident"

cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp -rf tests $dir_name