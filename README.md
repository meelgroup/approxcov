# ApproxCov & ApproxMaxCov

ApproxCov and ApproxMaxCov are algorithms for fast and scalable approximation of t-wise coverage of a test suite for large configurable systems.  
t-wise coverage is computed as a ratio between the number of distinct combinations of features within a given test suite and the number of distinct combinations of features satisfying constraints of a configurable system. The work proposes two algorithms to approximate each of the elements of the ratio. The approximation is guaranteed to be within (1 ± ε)-factor of the ground truth with probability at least 1 − δ where ε and δ are selected parameters.  
The implementation includes the following algorithms:  
1. **ApproxCov** algorithm approximating the number of distinct combinations of features within a given test suite assuming that all features have exactly 2 values. It can be found in `approxcov.py` script  
2. Extension of **ApproxCov** to the general case where features can have a finite number of values. It can be found in `approxcov_mv.py` script  
3. **ApproxMaxCov** algorithm approximating the number of distinct combinations of features satisfying constraints of a configurable system assuming that all features have exactly 2 values. It can be found in `approxmaxcov.py` script  
4. Extension of **ApproxMaxCov** to the general case where features can have a finite number of values. It can be found in `approxmaxcov_mv.py` script  

Within each script the algorithms to compute the ground truth are provided. These algorithms are adapted from [baital tool](https://github.com/meelgroup/baital). 

This work is by Eduard Baranov, Sourav Chakraborty, Axel Legay, Kuldeep S. Meel, and Vinodchandran N. Variyam to appear in ICSE'22.

## System Requirements

Linux OS with Python 3.6 or higher, pip3, and git.  
Tested on: Ubuntu 18.10, 20.04 and Debian 11.

## Installation

1. Install GMP: `sudo apt install libgmp-dev`
2. Install [ApproxMC4](https://github.com/meelgroup/approxmc) (*):
    1. `sudo apt install build-essential cmake`
    2. `sudo apt install zlib1g-dev libboost-program-options-dev libm4ri-dev`
    3. `git clone https://github.com/msoos/cryptominisat`
    4. `cd cryptominisat`
    5. `mkdir build && cd build`
    6. `cmake ..`
    7. `make`
    8. `sudo make install`
    9. `cd ../..`
    10. `git clone https://github.com/meelgroup/approxmc`
    11. `cd approxmc`
    12. `mkdir build && cd build`
    13. `cmake ..`
    14. `make`
    15. `sudo make install`
3. Install z3: `sudo apt install z3`
4. Install additional python library: `pip3 install pycosat`

*We used revisions 30c6787 of approxmc and 641f915 of cryptominisat.

## Benchmarks

Benchmarks can be found at [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.5883536.svg)](https://doi.org/10.5281/zenodo.5883536) 

## Common Assumptions on the Input Data

Configurable systems has a set of features and a set of constraints on them. We assume that features are numbered from 1 to nFeatures.  
Original algorithms were developed for the case where all features have exactly 2 possible values. In this case, we use the feature number to indicate that the feature is selected (or have value true) and its negation to indicate that the feature is not selected (or has value false). Constraints is this case are defined with Dimacs CNF format.  
The extension of the algorithms to the general case allows features that can have a finite number of values. In this case, all features shall have values between 0 and x-1, where x is the number of values the feature can have. Note that the feature with two values would also follow the format: their values would be 0 and 1. Constraints shall be defined with QF_BV logic and the input format is based on the SMT-LIB.

## ApproxCov

### Input format

Input file shall contain a set of configurations (test samples), 1 configuration per line. Each line starts with the configuration id (integer), followed by a comma, followed by a space-separated list of features sorted by a feature number. Each value in the list is either the feature number if the feature is selected (has value true) or its negation if the feature is not selected. Configuration id is ignored by the script.  

Example: the file containing the following 2 lines is a valid input file  
```
1, 1 2 3 -4 5
2, -1 -2 3 -4 5  
```

The file contains 2 configurations of a configurable system with 5 features: the first one selects features 1, 2, 3, and 5, and the second selects features 3 and 5.

The input file format coincides with the output format of baital and waps tools.

### Running

`python3 approxcov.py <arguments> ` from the `scripts` folder.

| Argument | Is Required | Default value | Description | 
| -------- | ----------- | ------------- | ----------- |
| samples | required | | a file with a set of configurations |
| --twise | required | | t value for t-wise coverage - size of feature combination |
| --approximate | optional | false | use approximate computations if set; compute ground truth otherwise |
| --delta | optional | 0.05 | delta parameter for PAC guarantees: approximation is guaranteed to be within (1 ± ε)-factor of the ground truth with probability at least 1 − δ |
| --epsilon | optional | 0.05 | delta parameter for PAC guarantees: approximation is guaranteed to be within (1 ± ε)-factor of the ground truth with probability at least 1 − δ |
| --seed | optional | | random seed; only applicable for approximate computations |

### Output

Console output contains two lines with the computed number of combinations and the time taken.
    
### Examples of use

`python3 approxcov.py --twise 2 ../benchmarks/two_values/samples/baital_4step.samples` \
would compute the exact number of feature combinations (ground truth) of size 2 in the `baital_4step.samples` file.

`python3 approxcov.py --approximate --twise 2 ../benchmarks/two_values/samples/baital_4step.samples` \
would compute the approximate number of feature combinations of size 2 in the `baital_4step.samples` file; the approximation is guaranteed to be within (1 ± 0.05)-factor of the ground truth with probability at least 0.95.

`python3 approxcov.py --approximate --epsilon 0.1 --delta 0.1 --seed 1 --twise 2 ../benchmarks/two_values/samples/baital_4step.samples` \
would compute the approximate number of feature combinations of size 2 in the `baital_4step.samples` file; the approximation is guaranteed to be within (1 ± 0.1)-factor of the ground truth with probability at least 0.9. `--seed` option sets the random seed, re-running the command would return the same approximation.

### Benchmarks

In the benchmarks referenced above, `two_values/samples/` folder contains a set of benchmarks used for evaluation of the approximation algorithm. All benchmarks have been generated from the configurable systems in `two_values/cnfs/`with three tools: baital, waps, and quicksampler. All benchmark filenames are composed as \<tool\>_\<configurable-system\>.samples.

## ApproxCov Extension

### Input format

The first line of input file contains a space-separated list of integers defining the number of values each feature can take ordered by the feature number. The following lines contain a set of configurations (test samples), 1 configuration per line. Each line starts with the configuration id (integer), followed by a comma, followed by a space-separated list of feature values sorted by a feature number. The value must be in range [0,n-1], where n is the number of values the feature can have and is defined in the first line of the file. Configuration id is ignored by the script.  
Example:  
```
2 3 4 5  
1, 0 2 1 0  
2, 1 0 0 4  
```

In the example, there are 4 features with 2, 3, 4, and 5 values, respectively, and 2 configurations.

The script `approxcov_mv.py` includes a function `rewrite_output_CASA` that can convert outputs of CASA tool [1] into the alogrithm's input format.

### Running & Output

`python3 approxcov_mv.py <arguments> ` from the `scripts` folder. Arguments are the same as for the ApproxCov.

### Examples of use

`python3 approxcov_mv.py --twise 2 ../benchmarks/mult_values/samples/benchmark1.samples` \
would compute the exact number of feature combinations (ground truth) of size 2 in the `benchmark1.samples` file.

`python3 approxcov_mv.py --approximate --twise 2 ../benchmarks/mult_values/samples/benchmark1.samples` \
would compute the approximate number of feature combinations of size 2 in the `benchmark1.samples` file; the approximation is guaranteed to be within (1 ± 0.05)-factor of the ground truth with probability at least 0.95.

`python3 approxcov_mv.py --approximate --epsilon 0.1 --delta 0.1 --seed 1 --twise 2 ../benchmarks/mult_values/samples/benchmark1.samples` \
would compute the approximate number of feature combinations of size 2 in the `benchmark1.samples` file; the approximation is guaranteed to be within (1 ± 0.1)-factor of the ground truth with probability at least 0.9. `--seed` option sets the random seed, re-running the command would return the same approximation.

### Benchmarks

In the benchmarks referenced above, `mult_values/samples/` folder contains a set of benchmarks used for evaluation of the approximation algorithm. Benchmarks have been taken from the evaluation materials of [1] and can be obtained [here](http://cse.unl.edu/~citportal/).


## ApproxMaxCov

### Input format

A CNF file in Dimacs CNF format.

### Running

`python3 approxmaxcov.py <arguments> ` from the `scripts` folder

| Argument | Is Required | Default value | Description | 
| -------- | ----------- | ------------- | ----------- |
| samples | required | | a file with a set of configurations |
| --twise | required | | t value for t-wise coverage - size of feature combination |
| --outputdir | optional | results | directory in which lists of feature combinations are stored for the ground truth computations |
| --approximate | optional | false | use approximate computations if set; compute ground truth otherwise |
| --delta | optional | 0.05 | delta parameter for PAC guarantees: approximation is guaranteed to be within (1 ± ε)-factor of the ground truth with probability at least 1 − δ |
| --epsilon | optional | 0.05 | delta parameter for PAC guarantees: approximation is guaranteed to be within (1 ± ε)-factor of the ground truth with probability at least 1 − δ |
| --seed | optional | | random seed; only applicable for approximate computations |

### Output

The last two lines of console output contain the computed number of combinations and the time taken.
    
### Examples of use

`python3 approxmaxcov.py --twise 2 ../benchmarks/two_values/cnfs/4step.cnf` \
would compute the exact number of feature combinations (ground truth) of size 2 in the `4step.cnf` file.

`python3 approxmaxcov.py --approximate --twise 2 ../benchmarks/two_values/cnfs/4step.cnf` \
would compute the approximate number of feature combinations of size 2 in the `4step.cnf` file; the approximation is guaranteed to be within (1 ± 0.05)-factor of the ground truth with probability at least 0.95.

`python3 approxmaxcov.py --approximate --epsilon 0.1 --delta 0.1 --seed 1 --twise 2 ../benchmarks/two_values/cnfs/4step.cnf` \
would compute the approximate number of feature combinations of size 2 in the `4step.cnf` file; the approximation is guaranteed to be within (1 ± 0.1)-factor of the ground truth with probability at least 0.9. `--seed` option sets the random seed, re-running the command would return the same approximation.

### Benchmarks

In the benchmarks referenced above, `two_values/cnfs/` folder contains a set of benchmarks used for evaluation of the approximation algorithm. The benchmarks are taken from the evaluation of [baital tool](https://github.com/meelgroup/baital) and from the [dataset](https:/doi.org/10.5281/zenodo.3793090).


## ApproxMaxCov Extension

### Input format

The file is a QF_BV logic representation of constraints in SMT-LIB format. The first line must start with `;;` (comment in SMT-LIB format) followed by a space-separated list integers defining the number of values each feature can take ordered by the feature number. Constraint representation starts by declaring bit-vectors for each feature and an assertion limiting the maximal value the feature can take. Other constraints are defined in form of assertions over the defined bit-vectors.
Example:
```
;; 2 3 2
(set-logic QF_BV)
(declare-fun v_0 () (_ BitVec 2))
(assert (and (bvuge v_0 (_ bv0 2)) (bvult v_0 (_ bv2 2))))
(declare-fun v_1 () (_ BitVec 2))
(assert (and (bvuge v_1 (_ bv0 2)) (bvult v_1 (_ bv3 2))))
(declare-fun v_2 () (_ BitVec 2))
(assert (and (bvuge v_2 (_ bv0 2)) (bvult v_2 (_ bv2 2))))
(assert (or (not (= v_0 (_ bv0 2))) (not (= v_1 (_ bv1 2)))))
```

The example above has 3 features that have 2, 3, and 2 values, respectively. Declare-funs and first three assertions define bitvectors and limit the maximal value a corresponding feature can have. The last assertion defines a constraint between the features.  
The script `approxmaxcov_mv.py` includes a function `parse_CASA_bv` that can convert inputs of CASA tool [1] into the algorithm's input format. 

### Running & Output

`python3 approxmaxcov_mv.py <arguments> ` from the `scripts` folder. Arguments are the same as for ApproxMaxCov.


### Examples of use

`python3 approxmaxcov_mv.py --twise 2 ../benchmarks/mult_values/smts/benchmark1.smt` \
would compute the exact number of feature combinations of size 2 in the `benchmark1.smt` file

`python3 approxmaxcov_mv.py --approximate --twise 2 ../benchmarks/mult_values/smts/benchmark1.smt` \
would compute the approximate number of feature combinations of size 2 in the `benchmark1.smt` file; the approximation is guaranteed to be within (1 ± 0.05)-factor of the ground truth with probability at least 0.95

`python3 approxmaxcov_mv.py --approximate --epsilon 0.1 --delta 0.1 --seed 1 --twise 2 ../benchmarks/mult_values/smts/benchmark1.smt` \
would compute the approximate number of feature combinations of size 2 in the `benchmark1.smt` file; the approximation is guaranteed to be within (1 ± 0.1)-factor of the ground truth with probability at least 0.9. `--seed` option sets the random seed, re-running the command would return the same approximation


### Benchmarks

In the benchmarks referenced above, `mult_values/smts/` folder contains a set of benchmarks used for evaluation of the approximation algorithm. Benchmarks have been taken from the evaluation materials of [1] and can be obtained [here](http://cse.unl.edu/~citportal/).


## Computation of t-wise Coverage

t-wise coverage is computed as a ratio between the number of distinct combinations of features within a given test suite and the number of distinct combinations of features satisfying constraints of a configurable system. Computation of the former is described in "ApproxCov" section and of the latter in "ApproxMaxCov" section. The approximation is guaranteed to be within (1 ± (ε1 + ε2)/(1-ε2))-factor of the ground truth with probability at least 1 − δ1 - δ2, where ε1, δ1 and ε2, δ2 are parameters of ApproxCov and ApproxMaxCov, respectively.


[1] Brady J Garvin, Myra B Cohen, and Matthew B Dwyer. 2009. An improved meta-heuristic search for constrained interaction testing. In 2009 1st International Symposium on Search Based Software Engineering. IEEE, 13–22.

