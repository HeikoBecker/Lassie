# Lassie

**IMPORTANT: This code is not actively maintained anymore**

The Case Studies for the CPP 2021 paper can be found in the folder `examples`.
Please make sure to install the dependencies and follow the setup guide below if
you intend to run them on your machine.

## Dependencies

To run Lassie you need to have a working HOL4 installation.
For this please refer to [https://github.com/HOL-Theorem-Prover/HOL].

To compile and run SEMPRE you need to have a working ruby installation.
The java `jar` command should also be available either from OpenJDK or Oracle Java.
Running the following command should on Debian based systems set up the dependencies correctly:

    apt-get install ant ruby2.7

## Setup

To run Lassie you need to first configure some environment variables.
Assuming you are in the directory to which the Lassie repository was cloned, run

    export LASSIEDIR=`pwd`
    echo "export LASSIEDIR=$LASSIEDIR" >> ~/.bash_profile

Now you can set up SEMPRE and build the Lassie support library

    cd $LASSIEDIR/sempre/
    ./pull-dependencies core interactive
    ant core interactive
    cd $LASSIEDIR/src
    $HOLDIR/bin/Holmake

## Using Lassie

The `examples` folder comes with an already preconfigured `Holmake` file. We
suggest to put new files in that directory to experiment with Lassie.

To use Lassie in a HOL4 script, add the following line after other included
libraries

    open LassieLib;

Running this command loads the functions from the Lassie library and starts
a SEMPRE instance.
Note that we currently support only one instance of SEMPRE being run.

Now you can use `nltac` as a drop-in replacement for any HOL4 tactic, sending
tactic descriptions to SEMPRE.
We recommend running the examples from the `examples` directory (files
`arithTactics.sml` and `realTactics.sml`) to get some predefined descriptions.

Also see the script files in that directory for examples how to use `nltac`.

Funtion `nlexplain` can be run similarly.
It must be put before starting the actual proof script:

    nlexplain()

    <Lassie tactics>

After sending `nlexplain()` to the HOL4 REPL, Lassie tactics can be send just
like normal HOL4 commands to the REPL.

If you want to use Holmake, you have to explicitly enforce no parallelism, using
`Holmake -j 1`.
In case there are any issues with `Holmake` please look at the [[Known Bugs]].

If you only want to test SEMPRE's grammar for Lassie, this can be done by running
the `run` script:

    $LASSIEDIR/sempre/interactive/run @mode=lassie

This will give you an interactive SEMPRE session where commands can be send to
SEMPRE and their parse according to the grammar is printed.

## Case Studies

The case studies for our CPP 2021 paper can be found in the directory `examples`.
File `caseStudy<N>` is the n-th case study from section 5 of the paper.

The file `gaussScript.sml` contains the prove of the closed formula for the sum
of the first n numbers, used as an example in our HOL4 tutorial.

The files `arithTacticsLib.sml`, `logicTacticsLib.sml` and `realTacticsLib.sml`
contain the calls to `def` setting up the Lassie tactics for the case studies
and the tutorial.

## Other directories

The directory `src` contains the main SML development of Lassie, connecting HOL4
to the semantic parser SEMPRE.

The directory `sempre` contains the version of SEMPRE that we have based the
development of Lassie on.
It is mostly based GitHub version (https://github.com/percyliang/sempre) of the paper
Berant, J., Chou, A., Frostig, R., and Liang, P. Semantic parsing on
Freebase from question-answer pairs. In Empirical Methods in Natural
Language Processing (EMNLP) (2013)/.

## Known Bugs

There is a known bug with HOL4, in that sometimes HOL4 will get hung up on
reading the SEMPRE output, especially when not running with `Holmake -j1`.
This can be seen by Holmake printing something along the lines of `invalid command: ...`.
If this happens please interrupt the process with `Ctrl-c` and restart `Holmake`.
