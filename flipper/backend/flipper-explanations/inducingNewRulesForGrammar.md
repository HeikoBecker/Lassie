# Inducing new rules
Relevant functions are `InteractiveMaster.induceRulesHelper`, `GrammarInducer.induceRules` and `DefinitionAligner.recursiveMatch`. The basics of inducing grammar are described in the section 5 of [Voxelurn paper](https://arxiv.org/abs/1704.06956). Our grammar induction differs only slightly (and the differences are mentioned in this document).

There are three main mechanisms of inducing rules:
 - highest scoring packings
 - simple packings
 - alignment
 - rephrasing the body (**experimental**)

Assume that user wrote `pick red` and upon parser not being able to understand it, it defined it with `pick item has color red`.  The original utterance, `pick red`, is called **head** (and in the paper it's denoted by `x`). The definition, `pick item has color red`, is called body (and in the paper denoted by `X`). Since parser was not able to understand **head**, there is no full derivation. However, the parser might be able to parse parts of it. The set of partial derivations is denoted by `chart(x)`. (In our example that would be `$Color -> red`, and `$ItemActionFragment -> pick`. Some of those partial derivations are particularly interesting: those that appear as part of the full derivation in the body `X` (formally, their formulas have to match). We call a set of such derivations *packing* if the derivations in the set are not overlapping. The packing is maximal if any new derivation would overlap to one of the members of packing.

## Highest scoring packings
Here we are looking for a maximal packing `P = [d1, d2, ..., dk]` for which `score(P) =  Σscore(d_i)` is maximal. (Score is defined in the section on parser, based on different properties of the parse). Then a new rule is created in which each derivation from `P` (and that is also shared in head `x`) replaces the corresponding part in body `X`. As an example consider head = `pick once there item has color red` and body `pick item has color red`. The body is parsed into `$Action -> $ItemActionFragment (pick) $CountedItem (item has color red)` The partial parses of the head are `P = [{$RelColor -> color, $CountedItem-> item, $Color -> red, $ItemActionFragment -> pick, $PropertySet -> has color red, $Item -> item, $Item -> item has color red, $CountedItem -> item has color red]`. (here, the derivation is written only as a description, `category -> utterance`. In reality it is fully unrolled). The best maximal packing here is `P* = [$ItemActionFragment -> pick, $CountedItem -> item has color red]`. After these categories are replaced in the body `X`, a new rule is induced `$Action -> $ItemActionFragment once there $CountedItem`

In the original Voxelurn code, if all right-hand side utterances are categories, the rule is disregarded. In our code this restriction is removed.

## Simple packings
This is a simpler way for generalization: the only derivations included in packings are those for primitive values. The simple categories are specified as an option (**link to the run file**). Simple categories in our system are $Color, $Direction, $Shape, $Point and $Number. For the running example and the full parse of the body
```
 $Action
 (   
   $ItemActionFragment
     pick
   $CountedItem
     $Item
       $PropertySet
         has
           $RelColor
             color  
           $Color
             red  
  )
```
the induced rule would be `$Action -> $ItemActionFragment once there item has color $Color`

## Alignment

**this section needs some more details**

This method infers rules from the similarities between the utterance and the definition (It only works if a definition is a single command.) Consider the example with head being `take item has color red` and the body `pick item has color red`. By aligning these two utterances, a new rule is provided `$ItemActionFragment -> take` (with the meaning of `pick`). There are few restrictions to aligning mechanism:
 - it only aligns two utterances if their lengths differ for at most 3 (can be tweaked by `DefinitionAligner.maxLengthDiffernce` option)

- if all but 1 pair of short spans (1 or 2 tokens) are matched (the same), the unmatched pair is aligned

- in the original Voxelurn code, as soon as one alignment is found, the method returns. (In our code it continues the search.)

## Rephrasing body [**experimental**]
The idea is that before the previously mentioned three methods take place, instead of using the body provided by the user, we can use that body and few more bodies, inferred by the system. The intuition behind it and some potential methods are described [here](https://gitlab.mpi-sws.org/gavran/naturalizing-robotic-language/milestones/1). The current implementation only supports rewriting of repeated actions into loops and this can be turned on by setting the option `GrammarInducer.useLoopRewriting` to `true`.
