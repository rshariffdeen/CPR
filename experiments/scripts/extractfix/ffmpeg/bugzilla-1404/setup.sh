project_name=ffmpeg
bug_id=bugzilla-1404
dir_name=$1/extractfix/$project_name/$bug_id
project_url=https://github.com/FFmpeg/FFmpeg.git
commit_id=1e42736

deps_path=$1/extractfix/$project_name/ffmpeg-deps
current_dir=$PWD
[ ! -d $deps_path ] && mkdir $deps_path && cp ../build_ffmpeg.sh $deps_path && cd $deps_path && bash build_ffmpeg.sh
cd $current_dir

mkdir -p $dir_name
cp -rf deps $dir_name
cd $dir_name/deps
clang -c -fPIC hook.c -o hook.o
ar rcs libhook.a -o hook.o
clang -shared -o libhook.so hook.o

cd $dir_name
git clone $project_url src
cd src
git checkout $commit_id
cp $current_dir/Makefile $dir_name/src
cp $current_dir/configure $dir_name/src
cp $current_dir/../afl_driver.cpp $dir_name/src


grep -rl 'fabs' . | grep "\.c" | xargs sed -i -e 's/fabs(/fabs_fk(/g'
grep -rl 'fabs' . | grep "\.c" | xargs sed -i "1i #include<hook.h>"
git add -A
git commit -m 'change fabs to fabs_fk'
#
#sed -i 's/av_mallocz(avctx->width \* avctx->height)/malloc(avctx->width * avctx->height)/' libavcodec/dfa.c
#sed -i 's/av_cold //' libavcodec/dfa.c
#sed -i 's/NULL_IF_CONFIG_SMALL("Chronomaster DFA")/"Chronomaster DFA"/' libavcodec/dfa.c

sed -i '180i TRIDENT_OUTPUT("obs", "i32", frame_end - frame - width - 4);' libavcodec/dfa.c
sed -i "178d" libavcodec/dfa.c
sed -i '178i if (__trident_choice("L816", "i32", (int[]){width, frame_end, frame}, (char*[]){"x", "y", "z"}, 3, (int*[]){}, (char*[]){}, 0))' libavcodec/dfa.c
sed -i '32i #ifndef TRIDENT_OUTPUT\n#define TRIDENT_OUTPUT(id, typestr, value) value\n#endif\n' libavcodec/dfa.c
git add libavcodec/dfa.c
git commit -m "instrument trident"



cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__  -I${dir_name}/deps/  -L${dir_name}/deps/ -lhook -Wno-everything"
CC=$TRIDENT_CC
CXX=$TRIDENT_CXX
CFLAGS="$cflags"
CXXFLAGS="$cflags"


FFMPEG_DEPS_PATH=/data/extractfix/ffmpeg/ffmpeg-deps/libs/

PKG_CONFIG_PATH="$FFMPEG_DEPS_PATH/lib/pkgconfig" CFLAGS="-I$FFMPEG_DEPS_PATH/include $CFLAGS" ./configure \
    --cc=$CC --cxx=$CXX --ld="$CXX $CXXFLAGS -std=c++11" \
    --extra-ldflags="-L$FFMPEG_DEPS_PATH/lib" \
    --prefix="$FFMPEG_DEPS_PATH" \
    --pkg-config-flags="--static" \
    --enable-ossfuzz \
    --libfuzzer=$LIB_FUZZING_ENGINE \
    --optflags= \
    --enable-gpl \
    --enable-libass \
    --enable-libfdk-aac \
    --enable-libfreetype \
    --enable-libmp3lame \
    --enable-libopus \
    --enable-libtheora \
    --enable-libvorbis \
    --enable-libvpx \
    --enable-nonfree \
    --disable-muxers \
    --disable-protocols \
    --disable-devices \
    --disable-shared \
    --enable-cross-compile \
    --arch=x86_64 \
    --target-os=linux

make -j32 > /dev/null
subject=tools/target_dec_cavs_fuzzer
make ${subject}
cp ${subject} ./
KLEE_CFLAGS="-L/concolic-repair/lib -ltrident_runtime -L/klee/build/lib  -lkleeRuntest -lkleeBasic -lhook -L${dir_name}/deps/"
PROJECT_CFALGS="-std=c++11 -Llibavcodec -Llibavdevice -Llibavfilter -Llibavformat -Llibavresample -Llibavutil -Llibpostproc -Llibswscale -Llibswresample -L/data/ffmpeg/libs/lib  -Wl,--as-needed -Wl,-z,noexecstack -Wl,--warn-common -Wl,-rpath-link=libpostproc:libswresample:libswscale:libavfilter:libavdevice:libavformat:libavcodec:libavutil:libavresample -Qunused-arguments   libavdevice/libavdevice.a libavfilter/libavfilter.a libavformat/libavformat.a libavcodec/libavcodec.a libpostproc/libpostproc.a libswresample/libswresample.a libswscale/libswscale.a libavutil/libavutil.a -lavdevice -lavfilter -lavformat -lavcodec -lpostproc -lswresample -lswscale -lavutil -lass -lm -lharfbuzz -lfontconfig -lexpat -lfreetype -lexpat -lfribidi -lfreetype -lz -lpng12 -lz -lm -lva -lva-drm -lva-x11 -lxcb -lXau -lXdmcp -lxcb -lXau -lXdmcp -lxcb-xfixes -lxcb-render -lxcb-shape -lxcb -lXau -lXdmcp -lxcb-shape -lxcb -lXau -lXdmcp -L /data/ffmpeglibs/lib -lstdc++ -lm -lrt -ldl -lnuma -L/data/ffmpeg/libs/lib -lvpx -lm -lpthread -L/data/ffmpeg/libs/lib -lvpx -lm -lpthread -L/data/ffmpeg/libs/lib -lvpx -lm -lpthread -L/data/ffmpeg/libs/lib -lvpx -lm -lpthread -lvorbisenc -lvorbis -logg -ltheoraenc -ltheoradec -logg -L/data/ffmpeg/libs/lib -lopus -lm -L/data/ffmpeg/libs/lib -lopus -lm -lmp3lame -lfreetype -lz -lpng12 -lz -lm -L/data/ffmpeg/libs/lib -lfdk-aac -lm -lass -lm -lharfbuzz -lfontconfig -lexpat -lfreetype -lexpat -lfribidi -lfreetype -lz -lpng12 -lz -lm -lm -llzma -lz"
make ${subject}
wllvm -ggdb3 -Wall -W -o tools/target_dec_cavs_fuzzer tools/target_dec_cavs_fuzzer.o afl_driver.o ${PROJECT_CFALGS} ${KLEE_CFLAGS} -Wl,-rpath
extract-bc  ${subject}
# copy target bc to root dir
cp ${subject}.bc .

cd $current_dir
cp repair.conf $dir_name
cp spec.smt2 $dir_name
cp t1.smt2 $dir_name
cp -rf components $dir_name
cp exploit.mpg $dir_name
