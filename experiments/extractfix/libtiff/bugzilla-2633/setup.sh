project_name=libtiff
bug_id=bugzilla-2633
dir_name=$1/extractfix/$project_name/$bug_id
project_url=https://github.com/vadz/libtiff.git
commit_id=f3069a5


mkdir -p $dir_name
cd $dir_name
git clone $project_url src
git checkout $commit_id
cp exploit.tif $dir_name


