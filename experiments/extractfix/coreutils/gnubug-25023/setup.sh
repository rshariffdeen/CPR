project_name=coreutils
bug_id=gnubug-25023
dir_name=$1/extractfix/$project_name/$bug_id

project_url=https://github.com/coreutils/coreutils.git
commit_id=ca99c52


current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
git clone $project_url src
cd src
git checkout $commit_id


sed -i '1238i }' src/pr.c
sed -i '1236d' src/pr.c
sed -i '1236i CPR_OUTPUT("obs", "i32", col_sep_length);\n' src/pr.c
sed -i '1236i else if (!join_lines && *col_sep_string == \x27\\t\x27 && __cpr_choice("L290", "bool", (int[]){col_sep_length}, (char*[]){"col_sep_length"}, 1, (int*[]){}, (char*[]){}, 0)){' src/pr.c
sed -i '97i #ifndef CPR_OUTPUT\n#define CPR_OUTPUT(id, typestr, value) value\n#endif' src/pr.c
sed -i '97i #include <klee/klee.h>' src/pr.c
git add src/pr.c
git commit -m "instrument cpr"


./bootstrap
FORCE_UNSAFE_CONFIGURE=1 CC=$CPR_CC CXX=$CPR_CXX ./configure CFLAGS='-g -O0 -static -fPIE' CXXFLAGS="$CFLAGS"
make -j32
make CFLAGS="-fPIC -fPIE -L/klee/build/lib  -lkleeRuntest" CXXFLAGS=$CFLAGS src/pr -j32

cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp exploit.txt $dir_name



