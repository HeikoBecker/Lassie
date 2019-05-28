# Implementing the Dictionary
Relevant files are `Dictionary.java`, `DictionaryEntry.java`, and relevant functions are `InteractiveMaster.handleCommand` and `Grammar.readInducedGrammar`.
`Json.java` was used to handle converting objects into JSON strings and vice versa, particularly the functions `readValueHard` and `writeValueAsStringHard`.

## Generating the Dictionary. 
The list of induced rules is stored in `int-output/grammar.log.json`. The file is read by `Grammar.readInducedGrammar` and a list of JSON lines is returned by the function. 
The function is called from `Dictionary.compileDictionary`, and each JSON string is parsed into a rule, and the necessary information is filtered to create a DictionaryEntry. 
A list of DictionaryEntries is generated and converted into a JSON string by the function `Dictionary.jsonDictionary`.

## Communicating with front end
The communication with the front end is handled by `InteractiveMaster.handleCommand` (case command.equals(":dictionary"))`. 
`Dictionary.jsonDictionary` is called and the returned String is put in the response that is sent back to front end (using `stats.put` defined in `QueryStats.java`). 

## Deleting a rule
We will allow the user to delete a rule they have defined themselves. 
Relevant files are `InteractiveBeamParser.java`, `Trie.java`, `Parser.java`. Relevant functions are `InteractiveMaster.handleCommand` and `InteractiveUtils.removeRuleInteractive`.

### Deleting from the log files
After parsing the query in `InteractiveMaster.handleCommand` (case command.equals(":delete")), the grammar log is read and inconsistent results, such as the index of the rule to be deleted being higher than the number of rules in the file, or the session being unable to write grammar, stop the function.
The relevant JSon line is retrieved and parsed into a rule (using `Grammar.ruleFromJson`).
It is then deleted from the list of lines, and the grammar log is overwritten by the resulting list of lines, effectively deleting the rule from the induced rules.

### Deleting from the cached grammar
The grammar is not read each time a command is parsed, but rather stored by the parser for faster computation, so we need to delete the rule from the parser (`Parser.removeRule`).
The parser that is used by `InteractiveMaster` is `InteractiveBeamParser` where the grammar is stored in an ArrayList for cat-unary rules and in a Trie for non cat-unary rules, and `Parser.removeRule` is overriden in `InteractiveBeamParser.java`.
`InteractiveMaster.java` calls `InteractiveUtils.removeRuleInteractive` from where `InteractiveBeamParser.removeRule` is called or an Exception is thrown if the Parser used is not of the subclass `InteractiveBeamParser`. (similar to `addRuleinteractive`)
The function `Trie.remove` in `Trie.java` handles the removal of a rule from a Trie and the clean up that follows, and is used when deleting a non cat-unary rule.

Read more about implementing Dictionary in the front end [here](https://github.com/akshalaniche/flipper/blob/master/documentation/explanations/DictionaryFrontEnd.md) 
