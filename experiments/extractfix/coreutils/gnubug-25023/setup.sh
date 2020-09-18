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


./bootstrap
FORCE_UNSAFE_CONFIGURE=1 CC=$TRIDENT_CC CXX=$TRIDENT_CXX ./configure
make -j32

cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp exploit.j2k $dir_name



