project_name=coreutils
bug_id=bugzilla-19784
dir_name=$1/extractfix/$project_name/$bug_id

project_url=https://github.com/coreutils/coreutils.git
commit_id=658529a


mkdir -p $dir_name
cd $dir_name
git clone $project_url src
git checkout $commit_id


