project_name=coreutils
bug_id=bugzilla-19784
dir_name=$1/extractfix/$project_name/$bug_id

project_url=https://github.com/coreutils/coreutils.git
commit_id=658529a

current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
git clone $project_url src
cd src
git checkout $commit_id


sed -i '214,215d' src/make-prime-list.c
sed -i '214i while((__trident_choice("L290", "bool", (int[]){size, i}, (char*[]){"size","i"}, 2, (int*[]){}, (char*[]){}, 0)) && sieve[++i] == 0)' src/make-prime-list.c
sed -i '215i TRIDENT_OUTPUT("obs", "i32", size - i);\n' src/make-prime-list.c
git add src/make-prime-list.c
git commit -m "instrument trident"

./bootstrap
FORCE_UNSAFE_CONFIGURE=1 CC=$TRIDENT_CC CXX=$TRIDENT_CXX ./configure
make -j32

cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name


