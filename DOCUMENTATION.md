# LASSIE - Naturalizing theorem prover tactic languages

## Grammar
From SEMPRE's documentation, a rule has the following form

	(rule <target-category> (<source-1> ... <source-k>) <semantic-function>)

### Using functions
We are currently piggy-backing on the DALExecutor for semantics, which creates a custom world for Lassie called `TacticWorld`. There are several layers to evaluation. Lambda expressions are reduced by SEMPRE's Java executor. The beta-reduced term is a command for the DALExecutor.

Commands of the form `(: cmd arg1 arg2 ...)` are Action Formulas: as Java definitions, they return void but have an effect on their world.

Commands of the form `(call cmd arg1 arg2 ...)` are Call Formulas: as Java definitions, they can return values and thus, be composed.

Both Action and Call Formulas have their `cmd` part defined as functions in the `TacticWorld` class.

### Tips
- On the source side of a rule definition, don't hug brackets to their content; e.g. instead of `[$Head, $Tail]`, write `[ $Head , $Tail ]` and instead of `[]`, write `[ ]`.
