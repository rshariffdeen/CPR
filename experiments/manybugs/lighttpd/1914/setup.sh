project_name=lighttpd
bug_id=1914
dir_name=$1/manybugs/$project_name/$bug_id
download_url=https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/lighttpd-bug-1913-1914.tar.gz
current_dir=$PWD
mkdir -p $dir_name
cd $dir_name
wget $download_url
tar xfz lighttpd-bug-1913-1914.tar.gz
mv lighttpd-bug-1913-1914 src
rm lighttpd-bug-1913-1914.tar.gz
mv src/* .
rm -rf src
rm -rf  coverage* \
        configuration-oracle \
        local-root \
        limit* \
        *.cache \
        *.debug.* \
        sanity \
        compile.pl \
        *~ \
        test \
        reconfigure \
        preprocessed \
        fixed-program.txt
mv bugged-program.txt manifest.txt
mv *.lines bug-info
mv fix-failures bug-info
mv lighttpd src
cd $dir_name/src
make distclean
svn upgrade
svn revert $(cat $dir_name/manifest.txt)
chown -R root $dir_name

cd $dir_name

# fix the test harness and the configuration script
sed -i "s#/root/mountpoint-genprog/genprog-many-bugs/lighttpd-bug-1913-1914#/data/manybugs/lighttpd/1914/#g" test.sh
sed -i "s#/data/manybugs/lighttpd/1914/src/limit#timeout 5#g" test.sh
sed -i "s#/usr/bin/perl#perl#g" test.sh
sed -i 's#lt-\.\*#lt-\.\* \&\> /dev/null#g' test.sh
sed -i 's#cd lighttpd/tests#pushd /data/manybugs/lighttpd/1914/src/tests#g' test.sh
sed -i 's#cd ../../#popd#g' test.sh

# fix an obnoxious bug in tests/core-request.t
sed -i 's#image.JPG#image.jpg#g' src/tests/core-request.t

# fix broken symlinks
cd src/tests/tmp/lighttpd/servers/www.example.org/pages
rm symlinked index.xhtml
ln -s expire symlinked
ln -s index.html index.xhtml

# fix broken test file
cp $current_dir/mod-cgi.t /data/manybugs/lighttpd/1914/src/tests/mod-cgi.t

# compile program
cd $dir_name/src
make clean
CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --with-pcre=yes --with-ldap --with-bzip2 --with-openssl --with-gdbm --with-memcache --with-webdav-props --with-webdav-locks
#CC=wllvm CXX=wllvm++ ./configure CFLAGS='-g -O0' --enable-static --disable-shared --with-pcre=yes --with-ldap --with-bzip2 --with-openssl --with-gdbm --with-memcache --with-webdav-props --with-webdav-locks
CC=wllvm CXX=wllvm++ make CFLAGS="-march=x86-64" -j32

#sed -i 's/fabs/fabs_cpr/g' libtiff/tif_luv.c
#sed -i 's/fabs/fabs_cpr/g' tools/tiff2ps.c
#git add  libtiff/tif_luv.c tools/tiff2ps.c
#git commit -m 'replace fabs with proxy function'
#make CC=$CPR_CC -j32

#sed -i '118d;221d' libtiff/tif_jpeg.c
#sed -i '153d;2429d' libtiff/tif_ojpeg.c
#git add libtiff/tif_ojpeg.c libtiff/tif_jpeg.c
#git commit -m 'remove longjmp calls'

make CFLAGS="-lcpr_proxy -L/CPR/lib -g" -j32
# Patch
#sed -i '748i if (con->request.content_length > 0) {' mod_cgi.c
# Trident
#sed -i '748i if (__cpr_choice("L748", "bool", (int[]){con->request.content_length, i}, (char*[]){"con->request.content_length","i"}, 2, (int*[]){}, (char*[]){}, 0))) {' mod_cgi.c
#sed -i '750i }' mod_cgi.c
#sed -i '353i { CPR_OUTPUT("obs", "i32", count);\n if (count < 0) klee_abort();\n' tools/gif2tiff.c
#sed -i '352d' tools/gif2tiff.c
#sed -i '352i while ((count = getc(infile)) &&  count <= 255 && (__cpr_choice("L65", "bool", (int[]){count, status}, (char*[]){"x", "y"}, 2, (int*[]){}, (char*[]){}, 0)) )' tools/gif2tiff.c
#sed -i '43i #ifndef CPR_OUTPUT\n#define CPR_OUTPUT(id, typestr, value) value\n#endif\n' tools/gif2tiff.c
#git add tools/gif2tiff.c
#git commit -m "instrument cpr"

#cd $current_dir
#cp repair.conf $dir_name
#cp spec.smt2 $dir_name
#cp t1.smt2 $dir_name
#cp -rf components $dir_name
#cp -rf tests $dir_name
