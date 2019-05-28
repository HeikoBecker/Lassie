# Implementing the Dictionary
Relevant files for the front end are `Dictionary/index.js`, `Dictionary/styles.css`, `actions/world.js` and `store/world.js`.

The dictionary requests the list of induced rules from the back end and renders a table of the rules to the screen. 

The store is used to request the rules and pass them to the dictionary.

## Requesting the rules from the back end
The function `Actions.dictionary` in `actions/world.js` calls `SEMPREquery` from `helpers/sempre.js` which sends a request to the backend. 
After processing of the request by the back end, a response is received by the `dictionary` function.

The function parses the JSON string and dispatches an action of type `dictionary` to the store. 
The reducer defined in `store/world.js` passes the dictionary to the state of the store. 

## Adding a new rule
When adding a new rule, the dictionary is reset to be empty, which forces the dictionary to send a request and reflect the changes to the log files.
However, this solution to a previous bug where the dictionary was not updating consistently because of asynchronous calls doesn't solve the bug for when the dictionary is initially empty, and a reload button was added for the user to force a new dictionary request.

## Deleting an induced rule
The option is offered to the user to delete a rule they have previously defined themselves. 
They can see the button only if their session ID matched the ID of the user who defined that rule.
As of now, the deletion affects the log files, and is not reversible.
Deleting a rule dispatches an action of type `dictionary` with an empty dictionary that forces the dictionary to be requested again by the system, and updates the front end to reflect the changes in back end.

Read more about implementing Dictionary in the back end [here](https://github.com/akshalaniche/sempre-interactive-flipper/blob/master/DictionaryBackEnd.md)
