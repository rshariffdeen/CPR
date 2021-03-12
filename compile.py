import os
from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext
source_dir = os.getcwd()
source_list = [f for f in os.listdir(source_dir) if os.path.isfile(os.path.join(source_dir, f))]
filtered_source_list = []
for source_file in source_list:
    if source_file != __file__ and ".py" in source_file:
        filtered_source_list.append(source_file)
ext_modules = [Extension("cpr", filtered_source_list)]

setup(
    cmdclass={'build_ext': build_ext},
    ext_modules=ext_modules
)
