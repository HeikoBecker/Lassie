# Rephrasing Formulas
As described [here](https://gitlab.mpi-sws.org/dashboard/milestones/reformulating-formulas-for-better-generalization?title=Reformulating+formulas+for+better+generalization), we want to do the rephrasing in the space of formulas. That will give us a greater generalization power.

## EquivalentFormulas
Class `EquivalentFormulas` is an abstract class that defines one method, `getEquivalentFormulas` that any other class should implement in order to support rephrasing formulas.

## Workflow
From `InteractiveMaster`, inside the function `induceRulesHelper` a `GrammarInducer` class is instantiated. In the options of that class we specify which methods of rephrasing to use and then add all the *rephrased formulas* into the list `derivationsToTry`. Finally, that list is used to get the right packings that are scored and the generalization is produced. **Is this the right architecture? Currently, aligning happens outside `GrammarInducer`, which means that aligning can't take the advantage of rephrased formulas**

## Implemented Rephrasings

 - `SimpleEquivalentRewriting`
 <br /> It tries to do rewriting of repeated formulas into loops (one part of Issue #20). It is able to rewrite `a;a;a;b`, but it is not able to rewrite `a;b;a;b`.
