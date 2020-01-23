# LASSIE - Documentation
This document addresses some technical details of Lassie. If you haven't
already, read the [introduction to Lassie](INTRODUCTION.md).

## SEMPRE
Lassie is designed as an extention of
[SEMPRE](https://nlp.stanford.edu/software/sempre/). You can take a look
at SEMPRE's [tutoral](sempre/TUTORIAL.md) and
[documentation](sempre/DOCUMENTATION.md). Lassie does not exploit all of
SEMPRE's application-specific features, but it does follow its general
form.

### Interactive Mode
There is little existing documentation on the SEMPRE's interactive
mode. One can refer to the [Voxelurn
paper](https://arxiv.org/pdf/1704.06956.pdf) and the [Flipper
paper](https://arxiv.org/pdf/1803.02238.pdf) for details on SEMPRE's
process of inductive learning. 

## Working on Lassie
As a framework, SEMPRE has different ports of access which one uses to
fit it to a particular context, namely the grammar, the lexicon and the
logical form semantics. In lassie, the lexicon is replaced by the
database, which not only introduces natural forms of logical entities
(as does the lexicon), but associate those entities together to build
domain knowledge.

### The Database
The database is currently located at
[sempre/interactive/lassie.db](sempre/interactive/lassie.db). The idea
behind the database is an extension of what SEMPRE's overnight mode's
database, in a slightly more compact form. At each line, we have a
triple:

    <entity>        <attribute>        <value1, value2, ...>

For example:

    rename        type      term quotation list -> tactic
    rename        name      alpha conversion, renaming
    rename        VP        rename, change
    rename        OBJ       variables, variable names, free variables

Lassie creates a lexicon file
[sempre/interactive/lassie.lexicon](sempre/interactive/lassie.lexicon)
which indicates the parser which word to parse into what logical form
(logical forms are generated to look like `<attribute>.<value>`). It
will create a lexeme for each attribute-value pair it encounters in the
database. Then, with the grammar rule

    (rule <new_category> ($PHRASE) (SimpleLexiconFn (type <attribute>)))

Lassie will parse values marked under attribute `<attribute>` in the
database, into the syntactic category `<new_category>`, which can be
used in other rules to build up full expressions. For example:

    (rule $name ($PHRASE) (SimpleLexiconFn (type name)))

Lassie also keeps the ontology accessible to its semantics so it gets
read when logical forms get executed.

#### Special Attributes
The `type` attribute is the only one required for each component and
gives rise to literal lexemes to be parsed into their fitting type in
the grammar; e.g. `asm_rewrite_tac` is given type `thm list -> tactic`
for which Lassie generates a lexeme

    lexeme:  "asm_rewrite_tac"
    formula: "asm_rewrite_tac"
    type:    "thmlist->tactic"

Calling `SimpleLexiconFn` on `(type thmlist->tactic)` captures all
instances of `asm_rewrite_tac` (and other functions of the same type)
into a category of choice—the current practice is just to call it
`$thmlist->tactic`. Note that internally, those types have their
whitespaces removed and parentheses turned into square brackets so type

    term quotation list -> (thm -> tactic) -> thm -> tactic

is actually fetched from SimpleLexiconFn with

    (type termquotationlist->[thm->tactic]->thm->tactic)

into a category potentially called

    $termquotationlist->[thm->tactic]->thm->tactic

### The Grammar
A SEMPRE grammar rule has the following form

    (rule <target-category> (<source-1> ... <source-k>) <semantic-function>)

where `<source-1> ... <source-k>` is a pattern made of text and
categories which will match an utterance or a derivation of it. Once
matched, SEMPRE can consider a derivation of category
`<target-category>` with the semantics given by
`<semantic-function>`. If one of the `<source-i>` is a category rather
than concrete text, then a derivation of that category can be bound and
substituted in the semantic function using lambdas, allowing logical
forms to compose into complex expression.

For example, the rules

    (rule $name ($PHRASE) (SimpleLexiconFn (type name)))
    (rule $set_hasName ($Name) (lambda n (call fromFeature (var n))))
    (rule $tactic_set (use tactic $hasName)
          (lambda s (call intersect (var s) (call fromFeature "type.tactic"))))

will parse the expression `use tactic res_tac` into the set of
components from the database which have `tactic` as type and `res_tac`
as name. In practice, we also add an `anchored` tag to the rules in
order to force derivations to constitute a single tree rooted at the
special category `$ROOT`. This allows us to build only well-typed HOL4
expressions: we restrict the ways in which logical forms can be composed
through function application by a fixed set of grammar rules. Thus our
rules look more like

    (rule $name ($PHRASE) (SimpleLexiconFn (type name)) (anchored 1))
    (rule $set_hasName ($Name) (lambda n (call fromFeature (var n))) (anchored 1))
    (rule $tactic_set (use tactic $hasName)
          (lambda s (call intersect (var s) (call fromFeature "type.tactic")))
          (anchored 1))

We will show how we turn sets of potential components into actual
components in the section about [ChoiceFn](#choicefn).

##### Note
It was observed experimentally that some users intuitively use theorems
as if they had effects, e.g. "distribute the multiplication", or "unfold
the definition", or "expand the product". In these utterances, the
activity of rewriting is left implicit. It would be beneficial for
usability to define the theorems with verbs of their effects. Effects,
however, are directed and although equalities at the base of HOL4
theorems often act as directed (in rewriting the LHS is rewritten into
the RHS), they internalize both directions. For example:

    val POW_2 = ⊢ ∀x. x pow 2 = x * x

"expands" in one way and "simplifies" in the other. Using `GSYM` is
necessary to get the "simplify" effect out of that theorem in the
context of rewriting. This could be mediated by counting `<thm>` and
`GSYM <thm>` as differently qualified, but related entities.

#### Miscellaneous
SEMPRE's lexing of utterances is sometimes different than its lexing of
the source (i.e. matching) side of a rule definition. Split tokens as
much as possible with spaces, e.g. don't hug brackets to their contents:
instead of `[$Head, $Tail]`, write `[ $Head , $Tail ]` and instead of
`[]`, write `[ ]`.

Parentheses need to be escaped. Double quotes also, although they
haven't been very much tested and would likely lead to breaks.

### The Semantics
Lassie's logical form semantics are written in the file
[TacticWorld.java](sempre/src/edu/stanford/nlp/sempre/interactive/lassie/TacticWorld.java). Because
our domain (HOL4 tactics) is dense in entities for which the names are
not well defined, a good part of the semantics exists to narrow down on
the specific components an utterance is referring to.

To achieve this, attributes are picked out in the sentence and cast into
the sets of components which posses said attribute. Through sensible
sentence construction, attributes are composed as their sets are
intersected. If a part of an utterance is sufficiently specific, then
its corresponding set contains a single element and the execution of its
logical form returns that single element.

#### ChoiceFn
SEMPRE provides a number of built-in semantic functions like
`SimpleLexiconFn` or `IdentityFn`. They differ from ordinary
`call`-formulas in that they do not show up in the resulting logical
form but help determine its derivation. They are executed during parsing
and can influence the direction of derivation. We have implemented the
`ChoiceFn` semantic function for purposes related to our set semantics.

Every set of potential components that aims to be an actual component
passes through `ChoiceFn`. On receiving a derivation which evaluates to
an empty set, `ChoiceFn` will kill that derivation, preventing further
derivations from branching off of it. On receiving a singleton set, it
will allow that set to be cast into the element contained in it. On
receiving a set with multiple elements, it will attempt to *abduce* the
simplest element of the set and allow the set to be cast to that
simplest element. If it fails to abduce an element, `ChoiceFn` will kill
the derivation and write an *ambiguity warning* to Lassie which can be
given to the user in the case where parsing failed to produce a single
derivation. Hopefully, this information about ambiguity can help the
user know what went wrong with their utterance.

The conditions for abducing `a` in a set of candidates `C` is that `a`
be a conceptual subset to all other components `c ∈ C`—meaning that all
of the attributes of that component also be attributes of all other
components of the set, i.e. iff `∀i.attributes(a) ⊆ attributes(cᵢ)`. For
example, we can have the following attributions:

    simp            VP      simplify
    simp            OBJ     goal

    fs              AV      full, fully
    fs              VP      simplify
    fs              OBJ     goal, all of goal, assumptions

    rfs             AV      reverse, full, fully
    rfs             VP      simplify
    rfs             OBJ     goal, all of goal, assumptions
    rfs             CP      in reverse order

Both `fs` and `rfs` build on `simp` in different ways; they are more
complex versions of the same functionality. Moreover, `rfs` will usually
only be used in cases where the order in which `fs` operates is not
satisfactory. We can capture this relation of increasing conceptual
complexity by defining them such that

    attributes(simp) ⊂ attributes(fs) ⊂ attributes(rfs)

Hence, calling for Lassie to "simplify" will parse to `simp` because it
can be abduced among `fs` and `rfs` as being the simplest of the
three. If the user cares that the assumptions also be simplified, then
they can specify further with something like "fully simplify" or
"simplify goal and assumptions".

##### Notes on ChoiceFn
`ChoiceFn` is special among semantic functions in that it executes
logical forms during derivation; the whole of SEMPRE appears to keep
derivation and execution of logical forms very separate. Making this
crossover was surprisingly friction-less and possibly better for running
time since it allows us to cull from the parsing derivations that are
meaningless.

`ChoiceFn`, as it is currently implemented, exists in two parts: the
semantic function (the actual `ChoiceFn`) and a logical form function
`choice` which does the abduction and casting part. We are currently
forced to wrap logical forms which execute to sets with a function call
returning a string because SEMPRE has a limited set of values it can get
from executing semantic functions (e.g. strings as StringValue, but we
do not have sets). Hence, in the grammar, every call to `ChoiceFn` is
done from a category that is uniquely construct-able from a rule having
as semantics

    (lambda s (call choice ... (var s) ...))

We could relax this condition if we made `ChoiceFn` wrap its child
derivation into a `choice` call, and then proceed with execution.
