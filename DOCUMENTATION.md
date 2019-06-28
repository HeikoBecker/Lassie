# LASSIE - Naturalizing theorem prover tactic languages

## Grammar

We are currently piggy-backing on the DALExecutor for semantics, which creates a custom world for Lassie called `TacticWorld`. There are several layers to evaluation. Lambda expressions are reduced by SEMPRE's Java executor. The beta-reduced term is a command for the DALExecutor.

Commands of the form `(: cmd arg1 arg2 ...)` are Action Formulas: as Java definitions, they return void but have an effect on their world.

Commands of the form `(call cmd arg1 arg2 ...)` are Call Formulas: as Java definitions, they can return values and thus, be composed.

Both Action and Call Formulas have their `cmd` part defined as functions in the `TacticWorld` class.
