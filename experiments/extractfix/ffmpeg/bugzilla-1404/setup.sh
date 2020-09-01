project_name=ffmpeg
bug_id=bugzilla-1404
dir_name=$1/extractfix/$project_name/$bug_id

project_url=https://github.com/jasper-software/jasper.git
commit_id=1e42736


mkdir -p $dir_name
cd $dir_name
git clone $project_url src
git checkout $commit_id
cp exploit* $dir_name


