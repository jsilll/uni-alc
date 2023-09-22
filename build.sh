#!/bin/bash

# Script exit on first error
set -e 

# Print commands as they are executed
set -x 

# Get the directory of this script
BASEDIR=$(dirname "$0")

# Change to the directory of this script
pushd "$BASEDIR"

# Build the project
cd build
cmake .. -DCMAKE_TOOLCHAIN_FILE=conan_toolchain.cmake -DCMAKE_BUILD_TYPE=Release
cmake --build .

# Move the executable to the root directory
mv src/Proj1 ../Proj1