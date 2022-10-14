project_name=libtiff
bug_id=bugzilla-2611
dir_name=$1/extractfix/$project_name/$bug_id
project_url=https://github.com/vadz/libtiff.git
commit_id=9a72a69

current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
git clone $project_url src
cd src
git checkout $commit_id


./autogen.sh
CC=wllvm CXX=wllvm++ ./configure --enable-static --disable-shared
CC=wllvm CXX=wllvm++ make -j32

sed -i 's/fabs/fabs_cpr/g' libtiff/tif_luv.c
git add  libtiff/tif_luv.c
git commit -m 'replace fabs with proxy function'

make CFLAGS="-lcpr_proxy -L/CPR/lib" -j32

sed -i '816i CPR_OUTPUT("obs", "i32", sp->bytes_per_line);' libtiff/tif_ojpeg.c
sed -i '816i if(__cpr_choice("L816", "bool", (int[]){sp->bytes_per_line, cc}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) return -1;\n' libtiff/tif_ojpeg.c
sed -i '178i #ifndef CPR_OUTPUT\n#define CPR_OUTPUT(id, typestr, value) value\n#endif\n' libtiff/tif_ojpeg.c
git add libtiff/tif_ojpeg.c
git commit -m "instrument cpr"


cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp exploit.tif $dir_name

