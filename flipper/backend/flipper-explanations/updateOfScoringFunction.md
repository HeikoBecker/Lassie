# Update of derivation scores

Each time Flipper presents potential parses of the utterance, they are ranked based on a scoring function. The scoring function depends on features such as which rules are fired in derivation, who is the author of the rule (and whether it's the same as the users), what is the topmost category... Then, the user chooses one of the offered parses. This choice is used to update parameters of the scoring function (which features will be considered important). This documents presents all the functions that take part in that update.

 - [InteractiveMaster.handleCommand](src/edu/stanford/nlp/sempre/interactive/InteractiveMaster.java#L190): the utterance is parsed without execution (and all parses are contained in variable `ex`) and the accepted formulas are contained in the var `targetFormulas` (in Flipper that will always be only one formula). `ex` and `targetFormulas` are then given as arguments to
 
 
 - [Learner.onlineLearnExampleByFormula](src/edu/stanford/nlp/sempre/Learner.java#L152): for each of the parses it sets variable `compatibility` to 1 if it was accepted, 0 otherwise. It calculates `counts`, a map from string (feature names) to floats by calling function `computeExpectedCounts` and then updates `params` by it.
 
 
 - [ParserState.computeExpectedCounts](src/edu/stanford/nlp/sempre/ParserState.java#L271): calculates log of reward based on compatibility (`logReward`)  and then assigns true score of a derivation `deriv` to `deriv.score` + `logReward`. (for non-default values of `opts.customExpectedCounts` it is done differently). The values of these scores are normalized and the increment is a difference between old score and a score with a reward (after normalizations). The incrementing happens in functions [Derivation.incrementAllFeatureVector](src/edu/stanford/nlp/sempre/Derivation.java#L391) and [FeatureVector.increment](src/edu/stanford/nlp/sempre/FeatureVector.java#L149)