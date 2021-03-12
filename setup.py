import os
from setuptools import setup, find_packages
from Cython.Build import cythonize
from distutils.core import setup


EXCLUDE_FILES = [
    'app/main.py',
    'app/synthesis.py'
]


def get_ext_paths(root_dir, exclude_files):
    """get filepaths for compilation"""
    paths = []

    for root, dirs, files in os.walk(root_dir):
        for filename in files:
            if os.path.splitext(filename)[1] != '.py':
                continue

            file_path = os.path.join(root, filename)
            if file_path in exclude_files:
                continue

            paths.append(file_path)
    return paths


setup(
    name='cpr',
    version='0.1.0',
    packages=find_packages(),
    ext_modules=cythonize(
        get_ext_paths('app', EXCLUDE_FILES),
        compiler_directives={'language_level': 3}
    )
)
