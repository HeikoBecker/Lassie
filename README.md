# Lassie

The Case Studies for the IJCAR 2020 paper can be found in the folder `examples`.
Please follow the below setup guide if you intend to run them on your machine.

## Dependencies

To run Lassie you need to have a working HOL4 installation.
For this please refer to [https://github.com/HOL-Theorem-Prover/HOL].

To compile and run SEMPRE you need to have a working ruby installation.
The java `jar` command should also be available either from OpenJDK or Oracle Java.

Lassie additionally depends on the shell variable `LASSIEDIR` which must point
to the folder where Lassie is stored (i.e. this directory)

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

To use `proveVerbose` the goal has to be started using function `gt` from the
goalTree package. If `! x. x < 3 ==> x < 5` is to be proven, run

    gt `! x. x < 3 ==> x < 5`;
    proveVerbose();

Afterwards natural language descriptions can be send just like normal HOL4
commands to the REPL.

If you want to use Holmake, you have to explicitly enforce no parallelism, using
`Holmake -j 1`.
In case there are any issues with `Holmake` please look at the [[Known Bugs]].

If you only want to test SEMPRE's grammar for Lassie, this can be done by running
the `run` script:

    $LASSIEDIR/sempre/interactive/run @mode=lassie

This will give you an interactive SEMPRE session where commands can be send to
SEMPRE and their parse according to the grammar is printed.

## Known Bugs

There is a known bug with HOL4, in that sometimes HOL4 will get hung up on
reading the SEMPRE socket file.
This can be seen by Holmake printing something along the lines of `invalid command: ...`.
If this happens please interrupt the process with `Ctrl-c` and restart `Holmake`.

## Case Studies

The case studies for our IJCAR 2020 paper can be found in the directory `examples`.
File `caseStudy<N>` is the n-th case study from section 5 of the paper.