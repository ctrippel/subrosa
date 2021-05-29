# subrosa

Subrosa is a tool for formally specifying leakage containment models (LCMs). It also provides automation to find leakage and is able to synthesize a suite of comprehensive litmus tests.

## Basic usage

No installation is needed! Just open the lcm_skeleton.als file in Alloy and execute it. If you want to visualize the results you can use the provided lcm.thm theme to hide superfluous edges. Alloy can be downloaded here: https://alloytools.org/download.html. We use Alloy 5 which requires Java 6.

## Synthesizing a Suite of Comprehensive Litmus Tests

To automatically generate a suite of interesting litmus tests follow the steps below. The generated set is minimal with respect to leakge.

### Prerequisites:

* Java 6
* Python

### Installation:

* `git clone https://github.com/beckus/AlloyAnalyzer`
* `cd AlloyAnalyzer`
* run `ant dist` to create an executable JAR file in the `dist` directory
* `cp $SUBROSA_HOME/MainClass.java edu/mit/csail/sdg/alloy4whole/`
* run `ant build` to build our *very slightly* customized command-line interface to Alloy

### Usage:

Basic usage: 

    java -cp AlloyAnalyzer/dist/alloy4.2.jar edu.mit.csail.sdg.alloy4whole.MainClass -f <uspec.als> [-n <num_instances>] <run_command> > <outfile>

Example usage:
    java -cp AlloyAnalyzer/dist/alloy4.2.jar edu.mit.csail.sdg.alloy4whole.MainClass -f lcm_perturbed.als test > test.out 

### Further Information
Further information on the usage can also be found at https://github.com/ctrippel/checkmate.
