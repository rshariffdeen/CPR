import os
from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext
source_dir = os.getcwd() + "/main"
source_list = [f for f in os.listdir(source_dir) if os.path.isfile(os.path.join(source_dir, f))]
ext_modules = []
for source_path in source_list:
    module_name = source_path.split("/")[-1].replace(".py", "")
    ext_modules.append(Extension(module_name, [source_path]))

setup(
    name='CPR',
    cmdclass={'build_ext': build_ext},
    ext_modules=ext_modules
)
