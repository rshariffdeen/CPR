project_name=libtiff
bug_id=bugzilla-2611
dir_name=$1/extractfix/$project_name/$bug_id
project_url=https://github.com/vadz/libtiff.git
commit_id=9a72a69


mkdir -p $dir_name
cd $dir_name
git clone $project_url src
git checkout $commit_id
cp exploit.tif $dir_name


