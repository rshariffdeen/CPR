bug_id=insertion_sort
dir_name=$1/svcomp/loops/$bug_id
project_url=https://github.com/sosy-lab/sv-benchmarks.git
program_dir=/data/svcomp/sv-benchmarks/c/loops
bench_dir=/data/svcomp/sv-benchmarks
[ ! -d $bench_dir ] && git clone $project_url $bench_dir
mkdir -p $1/svcomp/config
current_dir=$PWD

cp insertion_sort-1.c $program_dir
cd $program_dir
make CXX=$CPR_CXX CC=$CPR_CC  LDFLAGS="-lcpr_runtime -L/CPR/lib -L/klee/build/lib  -lkleeRuntest -I/klee/source/include" -j32 insertion_sort-1

cd $current_dir
mkdir -p $dir_name
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name

