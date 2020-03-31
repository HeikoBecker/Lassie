#An attempt at a new Lassie grammar which does not require the use of socket files

This grammar describes the **output** of SEMPRE such that it is easy to parse
back into SML code in polyML.
As before, we split the Lassie core grammar into two separate worls, the
tactics, and the commands.
Expressions in `<>` denote non-terminals.

```
    Lassie     ::= TACTICSTART <TACTIC> | COMMANDSTART <COMMAND>
    <TACTIC>   ::= PLAINTACTIC <TOKEN>
                   |THMLISTTACTIC <TOKEN> LISTSTART <THMLIST> LISTEND
                   |TERMTACTIC <TOKEN> TERMSTART <TERM> TERMEND
                   |TERMLISTTACTIC <TOKEN> LISTSTART <TERMLIST> LISTEND
    <THMLIST>     ::= EMPTY | <ELEMENTS>
    <ELEMENTS> ::= <TOKEN> | <TOKEN>, <ELEMENTS>
    <TERMLIST> ::= EMPTY | <TERMS>
    <TERMS>    ::= <TERM> | <TERM>, <TERMS>
    <COMMAND>  ::= COMMANDSTART <TOKEN> COMMANDEND
    <TOKEN>
```
