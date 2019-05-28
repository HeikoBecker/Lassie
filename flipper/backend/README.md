# SEMPRE INTERACTIVE - FLIPPER: Semantic Parsing with Execution, modified for usage in robotic world 
(based on original interactive sempre repository https://github.com/sidaw/sempre-interactive)

## What is SEMPRE and semantic parsing?

See [SEMPRE-DOCUMENTATION.md](/SEMPRE-DOCUMENTATION.md).

## What does this "Flipper" version of SEMPRE do?

This specific version of SEMPRE is a modification of the Voxelurn project which
uses SEMPRE as the basis for a block-building world where input utterances act
as build instructions for the block world (displayed with a browser-based
JavaScript application). This version SEMPRE spcifically models a simple
environment where a robot can move around a small map and pick/drop colored
items. In addition to using the core language to control the robot, a user can
define custom commands which are learned by the system improving its ability to
understand more natural language-style commands.

# Installation

## Requirements

You must have the following already installed on your system.

- Java 8 (not 7)
- Ant 1.8.2
- Ruby 1.8.7 or 1.9
- wget

Other dependencies will be downloaded as you need them. SEMPRE has been tested
on Ubuntu Linux 16.04, Debian 8, and MacOS X. Your mileage will vary depending
on how similar your system is.

## Easy setup

1. Clone this GitHub repository:

        git clone https://github.com/mpi-sws-rse/sempre-interactive-flipper.git (https)
        git clone git@github.com:mpi-sws-rse/sempre-interactive-flipper.git (ssh)

2. Download the minimal core dependencies (all dependencies will be placed in `lib`):

        ./pull-dependencies core

3. Compile the source code (this produces `libsempre/sempre-core.jar`):

        ant interactive

4. Run server (defaults to port 8410):

        ./interactive/run @mode=voxelurn

The command should execute, display some information about the grammar, and
wait for input from the browser client (server can be stopeed with `Ctrl+D`.
To go further with running sempre in the context of Robotic world, check
[Flipper](http://flipper.mpi-sws.org/#/about)

## Additional options

While rewriting user's definition (option `GrammarInducer.useEquivalentRewriting`), the rewritings are scored based on both best packing score and the semantic similarity (cosine similarity of average of words in the spec). In order to use semantic similarity (option `GrammarInducer.useSemanticSimilarityOfSentences`), you have to provide a file with trained vectors (e.g. from [GloVe](https://nlp.stanford.edu/projects/glove/)) and give a path to it in the option `InteractiveMaster.wordEmbeddingsFilePath`.

### General Troubleshooting

Here are some general tips for troubleshooting:

- If the browser client is acting weirdly
	- Pull the newest version for the repository (no need to restart yarn)
	- On the panel on the right side, press `Clear`
- If the code does not compile or immediately fails at runtime
	- Pull newest version of the code
	- Run `ant clean` and then `ant interactive`
- If the server throws an error during use with the browser client
	- Open an issue detailing the server-side error and the client-side input
- If all previously learned rules have to be forgotten, one can clean the file `sempre-interactive/int-output/grammar.log.json`

# Browser Client

The corresponding browser-based client to this project can be found
[here](https://github.com/mpi-sws-rse/flipper).