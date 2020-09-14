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



cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp exploit.j2k $dir_name


