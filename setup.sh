# Make ABC
pushd .
cd dependencies/abc
make libabc.a -j4
popd

# Make scalmc
pushd .
cd dependencies/scalmc
mkdir build
cd build
cmake ..
make -j4
# sudo make install
# sudo ldconfig
popd

echo "Done setting up dependencies"
echo "Please add ./dependencies/scalmc/build/lib/ to LD_LIBRARY_PATH"
