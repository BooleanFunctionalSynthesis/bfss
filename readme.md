# BFSS: Blazing Fast Skolem Synthesis

## Setup
BFSS has 2 major dependencies: [ABC](https://github.com/shubham-goel/ABC) and [Scalmc](https://github.com/shubham-goel/scalmcSampling). Both have been added as submodules in `./dependencies`. Note that some repos may be private. Please contact BFSS authors for access. Clone recursively to download dependencies and setup as follows:
```shell
# Download BFSS with dependencies
git clone --branch v4.1 git@github.com:Sumith1896/bfss.git
cd bfss
git submodule update --init dependencies/abc
git submodule update --init dependencies/scalmc # Skip if scalmc unavailable

# Setup Dependencies
sudo apt install libreadline-dev libboost-all-dev libm4ri-dev build-essential cmake
bash setup.sh
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$(pwd)/dependencies/scalmc/build/lib/
```
For persistent use, please add `./dependencies/scalmc/build/lib/` to the `$LD_LIBRARY_PATH` environment variable.

## Usage
Running `make [UNIGEN=NO] [BUILD=RELEASE/DEBUG]` builds BFSS. `UNIGEN=NO` compiles BFSS without the Scalmc dependency. Multiple binaries are created in `./bin/`:

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

## Citation
Please cite the corresponding conference paper:
```
@InProceedings{10.1007/978-3-319-96145-3_14,
author="Akshay, S.
and Chakraborty, Supratik
and Goel, Shubham
and Kulal, Sumith
and Shah, Shetal",
editor="Chockler, Hana
and Weissenbacher, Georg",
title="What's Hard About Boolean Functional Synthesis?",
booktitle="Computer Aided Verification",
year="2018",
publisher="Springer International Publishing",
address="Cham",
pages="251--269",
abstract="Given a relational specification between Boolean inputs and outputs, the goal of Boolean functional synthesis is to synthesize each output as a function of the inputs such that the specification is met. In this paper, we first show that unless some hard conjectures in complexity theory are falsified, Boolean functional synthesis must generate large Skolem functions in the worst-case. Given this inherent hardness, what does one do to solve the problem? We present a two-phase algorithm, where the first phase is efficient both in terms of time and size of synthesized functions, and solves a large fraction of benchmarks. To explain this surprisingly good performance, we provide a sufficient condition under which the first phase must produce correct answers. When this condition fails, the second phase builds upon the result of the first phase, possibly requiring exponential time and generating exponential-sized functions in the worst-case. Detailed experimental evaluation shows our algorithm to perform better than other techniques for a large number of benchmarks.",
isbn="978-3-319-96145-3"
}
```
