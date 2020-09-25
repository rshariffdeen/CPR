project_name=openjpeg
bug_id=github-169
dir_name=$1/extractfix/$project_name/$bug_id

project_url=https://github.com/uclouvain/openjpeg.git
commit_id=c02f145

current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
git clone $project_url src
cd src
git checkout $commit_id


autoreconf -i
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0 -static' CXXFLAGS="$CFLAGS"
make -j32

opj_file=applications/codec/j2k_to_image.c
opj_input=J2K_CFMT
sed -i "s/get_file_format(infile)/$opj_input/g" $opj_file
git add $opj_file
git commit -m "fix input format"

sed -i '470i TRIDENT_OUTPUT("obs", "i32", cp->tdx * cp->tdy); exit(255);' libopenjpeg/j2k.c
sed -i '470i if(__trident_choice("L515", "bool", (int[]){cp->tdx,cp->tdy}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) return;' libopenjpeg/j2k.c
sed -i '35i #ifndef TRIDENT_OUTPUT\n#define TRIDENT_OUTPUT(id, typestr, value) value\n#endif\n' libopenjpeg/j2k.c
git add libopenjpeg/j2k.c
git commit -m "instrument trident"



cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp exploit.j2k $dir_name

