# LASSIE - Introduction
Lassie is a semantic parser for HOL4's tactic language. Interaction with
Lassie is done through the following functions:

- `lassie : string -> int -> proof` Try and parse a natural language
  expression. Run it again with an index `n` to accept and apply the
  `n`th derivation to the current goal.
- `nltac : string -> tactic` A tactic version of `lassie` to compose
  among other tactics of a proof. Chooses the first derivation it finds.
- `def : string -> string list -> unit` Define a natural expression
  which may not parse in terms of a list of expressions which do
  parse. The definition is generalized the the new rules are added to
  the grammar for the session.
  
For example:

	> lassie "fully simplify goal";
	(* prints available derivations *)
	
	> lassie "fully simplify goal" 2;
	(* uses the second derivation to advance the goal *)
	
	> nltac "fully simplify goal";
	val it = fn: tactic
	
	> def "fsg" ["fully simplify goal"];
	val it = (): unit

## Semantic Parsing
Lassie is built on [SEMPRE](https://nlp.stanford.edu/software/sempre/),
a toolkit for parsing structured natural language into logical forms
which can then be executed into a denotation. This process forms a
communication pipeline from user commands in natural form to computer
answers. Applied to the domain of interactive theorem proving, this
principle has the potential to make interactive proving more accessible
to non-experts.

One can get acquainted with SEMPRE through its
[tutorial](sempre/TUTORIAL.md). The principle behind Lassie is still
similar to SEMPRE's: we define a core language with a lexicon (bank of
natural expressions) and a grammar (how to combine those expressions)
which allows us to parse *utterances* (natural language queries from a
user); we can also add new rules to the grammar to support more
utterances through inductive generalization.

The big picture of what SEMPRE does is turn natural language utterances
into *denotations* by the intermediate of a *logical form*. The logical
form is thought of as a program internalizing the meaning of the
utterance and the denotation is the result of its execution. For
example:

- utterance: `sum up the numbers between 0 and 10`
- logical form: `(call sum (call range 0 10))`
- denotation: `55`

## HOL4
The purpose of Lassie is to offer a natural language interface for
proving HOL4 theorems through tactics. As such, the denotation we aim
for is a HOL4 program of type `tactic`. HOL4 offers a number of tactics
parameterized by patterns, other tactics, theorems, etc. The challenge of
Lassie is therefore to capture those parameters in a natural form and
construct a well-typed tactic which can be applied to advance a proof
goal. For example:

- utterance: `rewrite goal with multiplication distribution over addition theorems`
- logical form: `(call app (call intersect (call fromFeature VP.rewrite) (call fromFeature type.thmlist->tactic)...)))`
- denotation: `rewrite_tac [REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB]`

### The Database
The database is the source of Lassie's domain knowledge. It is currently
a file located at
[sempre/interactive/lassie.db](sempre/interactive/lassie.db). At each
line, we have a triple:

    <entity>        <attribute>        <value1, value2, ...>

For example:

    rename        type      term quotation list -> tactic
    rename        name      alpha conversion, renaming
    rename        VP        rename, change
    rename        OBJ       variables, variable names, free variables

From those entries, Lassie builds its *ontology*: its knowledge of the
universe it operates in. Attributes can have multiple values for a same
component. Of the currently implemented attributes (`type`, `name`,
`VP`, `OBJ`, `AV`, `CP`, `PREARG`), most are *parts of speech* (POS)
determining how this attribute might appear in a sentence.

#### Supported Inputs
We limit our natural language input to a structured form following basic
English sentence construction. For an intuition of what kind of
constructions we want to allow, imagine the different *parts of speech*
(POS) as types:

    noun = o
    adjective = o -> o
    adverb = (o -> o) -> (o -> o)
    verb = o -> tactic

- Verbs are at the core of the sentence and mostly determine the tactic
  (or tactical) to be used. Adverbs may refine the meaning of the verb.
  (For simplicity, we restrict verbs to the imperative tense such that
  they only require an object but no subject.)
- Arguments to the verb (terms, theorems, numbers, and lists of terms
  and of theorems; of type `o`) are noun phrases. At the core of a noun
  phrase is a noun, which may be refined with an adjective, which in
  turn can be refined with an adverb.

Guided by this model, we can structure our natural language around
principles of well-typed sentences. We name theorems with nouns
(e.g. distributivity, symmetry, definition, etc.) refined with
adjectives (e.g. addition, multiplication, left, right). Tactical
components (tactics or functions which produce tactics) get the verbs
(e.g. simplify, resolve, assume, rewrite) and adverbs (e.g. reverse,
fully, once). We allow complements (complement phrases) for
both object components (e.g. of multiplication, over addition, on the
left) and tactical components (e.g. with normalization) for further
refinements.

Thus, we parse sentences like

- "do induction" (`Induct`)
- "do induction on \`a\`" (`Induct_on 'a'`)
- "rewrite once with addition association" (`once_rewrite_tac [REAL_ADD_ASSOC] `)
- "simplify goal and assumptions using multiplication distributivity
  theorems" (`fs [REAL_LDISTRIB, REAL_RDISTRIB, REAL_SUB_LDISTRIB, ...]`)
- "resolve assumptions together" (`res_tac`)

### The Semantics
The logical form associated with a parse is a program which (1) searches
Lassie's ontology for the components matching the expressions used in
the utterance and (2) creates a well-typed application of those
components. If an utterance is too general, Lassie might fail in
synthesizing a sensible tactic, unless it thinks it can *abduce* the
correct component.

#### Abduction
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
