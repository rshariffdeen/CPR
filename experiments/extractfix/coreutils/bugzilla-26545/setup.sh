project_name=coreutils
bug_id=bugzilla-26545
dir_name=$1/extractfix/$project_name/$bug_id

project_url=https://github.com/coreutils/coreutils.git
commit_id=8d34b45

current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
git clone $project_url src
cd src
git checkout $commit_id

sed -i '292i klee_assert(i > size / 2 );\n' src/shred.c
sed -i '292i TRIDENT_OUTPUT("obs", "i32", i - (size/2));\n' src/shred.c
sed -i '290d' src/shred.c
sed -i '290i for(i = 3; (__trident_choice("L290", "bool", (int[]){size, i}, (char*[]){"size","i"}, 2, (int*[]){}, (char*[]){}, 0)); i *= 2)' src/shred.c
sed -i '97i #ifndef TRIDENT_OUTPUT\n#define TRIDENT_OUTPUT(id, typestr, value) value\n#endif' src/shred.c
sed -i '97i #include <klee/klee.h>' src/shred.c
git add src/shred.c
git commit -m "instrument trident"

./bootstrap
FORCE_UNSAFE_CONFIGURE=1 CC=$TRIDENT_CC CXX=$TRIDENT_CXX ./configure CFLAGS='-g -O0 -static -fPIE' CXXFLAGS="$CFLAGS"
make CFLAGS="-fPIC -fPIE -L/klee/build/lib  -lkleeRuntest -I/klee/source/include" CXXFLAGS=$CFLAGS -j32
make CFLAGS="-fPIC -fPIE -L/klee/build/lib  -lkleeRuntest -I/klee/source/include" CXXFLAGS=$CFLAGS src/shred -j32

cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp exploit.txt $dir_name
