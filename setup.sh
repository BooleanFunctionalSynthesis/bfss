# Make ABC
pushd .
cd dependencies/abc
make libabc.a -j4
popd

# Make scalmc
pushd .
cd dependencies/scalmc
if [ -z "$(ls -A .)" ]; then
   echo "Directory Empty, Skipping Scalmc build"
else
    echo "Building Scalmc"
    mkdir build
    cd build
    cmake ..
    make -j4
    # sudo make install
    # sudo ldconfig
fi
popd

echo "Done setting up dependencies"
echo "Please add ./dependencies/scalmc/build/lib/ to LD_LIBRARY_PATH"
