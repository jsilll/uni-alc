#!/bin/bash

# Script exit on first error
set -e 

# Print commands as they are executed
set -x 

# Get the directory of this script
BASEDIR=$(dirname "$0")

# Change to the directory of this script
pushd "$BASEDIR"

# Remove build directory if it exists
rm -rf build

# Detect the current platform
conan profile detect --force

# Install dependencies in build/
conan install . --output-folder=build --build=missing