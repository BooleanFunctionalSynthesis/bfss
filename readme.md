# BFSS: Blazing Fast Skolem Synthesis

## Setup
BFSS has 2 major dependencies: [ABC](https://github.com/shubham-goel/ABC) and [Scalmc](https://github.com/shubham-goel/scalmcSampling). Note that some repos may be private. Please contact BFSS authors for access. Modified version of both libraries should be placed in `./dependencies` and used as is. Setup dependencies as follows:
```
apt install libreadline-dev libboost-all-dev libm4ri-dev
bash setup.sh
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$(pwd)/dependencies/scalmc/build/lib/
```
For persistent use, please add `./dependencies/scalmc/build/lib/` to the `$LD_LIBRARY_PATH` environment variable.

## Usage
Running `make` builds multiple binaries in `./bin/`:

1. readCnf
2. genVarOrder
3. bfss
4. verify

readCnf is for converting qdimacs files to verilog files. Running `./readCnf benchmark.qdimacs` creates 2 new files in the working directory: `benchmark.v` and `benchmark_vars.txt` (list of variables to be eliminated)

`genVarOrder` takes `.v` and `_vars.txt` files as input and finds a heuristically sound variable ordering to be used. This ordering is printed to stdout, you'll have to redirect it to a file. You should run `./genVarOrder benchmark.v benchmark_vars.txt > benchmark_varstoelim.txt`

`bfss` runs the BFSS algorithm on an input AIG and variable ordering. It saves generated skolem functions to `benchmark_result.v`

`verify` verifies generated skolem functions. Run as `./verify benchmark.v benchmark_result.v benchmark_varstoelim.txt`

So a typical sequence of commands for working on a qdimacs would be as follows.
```
./readCnf benchmark.qdimacs
./genVarOrder benchmark.v benchmark_vars.txt > benchmark_varstoelim.txt
./bfss benchmark.v benchmark_varstoelim.txt -felut 3 --checkWDNNF (optionally add --useBDD to use the BDD pipeline)
./verify benchmark.v benchmark_result.v benchmark_varstoelim.txt
```

## Benchmarks
Benchmarks can be found [here](https://github.com/shubham-goel/Skolem_Benchmarks)
