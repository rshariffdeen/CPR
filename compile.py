import os
from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext
source_dir = os.getcwd()
source_list = [f for f in os.listdir(source_dir) if os.path.isfile(os.path.join(source_dir, f))]
filtered_source_list = []
ext_modules = []
for source_file in source_list:
    if source_file != __file__ and ".py" in source_file and source_file != '__init__.py':
        module_name = source_file.replace(".py", "")
        ext_modules.append(Extension(module_name, [source_file]))

setup(
    cmdclass={'build_ext': build_ext},
    packages=["cpr"],
    ext_modules=ext_modules
)
