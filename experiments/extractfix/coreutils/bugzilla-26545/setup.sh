project_name=coreutils
bug_id=bugzilla-26545
dir_name=$1/extractfix/$project_name/$bug_id

project_url=https://github.com/coreutils/coreutils.git
commit_id=8d34b45


mkdir -p $dir_name
cd $dir_name
git clone $project_url src
cd $dir_name/src
git checkout $commit_id

./bootstrap
FORCE_UNSAFE_CONFIGURE=1 ./configure


