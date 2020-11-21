bug_id=addition
dir_name=$1/svcomp/recursive/$bug_id
project_url=https://github.com/sosy-lab/sv-benchmarks.git
program_dir=/data/svcomp/sv-benchmarks/c/recursive
bench_dir=/data/svcomp/sv-benchmarks
[ ! -d $bench_dir ] && git clone $project_url $bench_dir
mkdir -p $1/svcomp/config
current_dir=$PWD

cp Addition02.c $program_dir
cd $program_dir
make CXX=$TRIDENT_CXX CC=$TRIDENT_CC  LDFLAGS="-ltrident_runtime -L/concolic-repair/lib -lkleeRuntest -I/klee/source/include" -j32 Addition02

cd $current_dir
mkdir -p $dir_name
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name

