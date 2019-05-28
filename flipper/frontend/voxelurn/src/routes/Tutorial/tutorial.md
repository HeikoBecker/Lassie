# Tutorial

Welcome to the tutorial! Here we will teach you the basics of using the system,
controlling the robot, and defining new commands for the robot.
Please complete this tutorial step-by-step so you get
a complete understanding of the system.
You can follow along with this tutorial by opening
the <a href="/#/build" target="_blank">build page</a> in a new window.

## Basics System Usage

Here you can find the basic ways to interact with the system.
- Basic usage
  - After typing in a command (try `move left`), press enter to see a preview of 
    the possible result(s)
  - Press enter again to accept the action (you do not have to wait for the
    action to finish)
  - You can undo an accepted action by clicking on the "x" next to the command 
    history
  - If you enter a command incorrectly (`move leftt`), the system will give you an 
    opportunity to define the command, click the "x" to cancel and edit the 
    command
  - All commands can be cleared: just press the blue "RESET" button.

If you need a quick reminder of command syntax, see these
[examples](/#/reference).

## Learning the Basic Commands


The following commands introduce you to the basics of the core language which
describes the individual actions that the robot can perform. After learning
a command, try using the command with different parameters (e.g., colors,
numbers, locations).

** Picking, dropping and visiting **
- Type `visit [5,8]` and  `move left`: you can specify movement by coordinate
or by direction 
  - If it is not possible to visit a point (e.g., it is a wall), _the robot will
  do nothing_
  - __Tip:__ any action can be repeated with the following syntax `repeat 2 times move left`
  - Before you accept the action, you can edit the command and try something else
- `pick item` will pick an item (you must be on the
same square as an item in order to pick it up) and `pick every item` will pick all the items on the square
  - `pick item is blue` will only pick a blue item (and similarly `pick item is triangle`)
  - __Tip:__ you can perform multiple actions sequentially by separating them with
  `;`; for example: `pick item; pick item is circle`
  - `is blue or is red` specifies disjunction (`or`) of properties
-  `drop item` works in the same manner
  -  commands of the kind `drop every item` will perform the action (`pick` or `drop`) on all items
  - Color specification works similarly: `drop every item is blue`
- Colors and shapes can be combined: `pick item is red and is triangle` will pick a red triangle, if there is one on robot's current spot
	- __Tip:__ if explicit grouping is needed, it can be done using curly braces, e.g. `pick item {not is red} and {is triangle}`
-  `visit room5` will send the robot to one of the points contained
in `room5` (room5 is an area, a set of points)
  - Areas can be explicitly defined: `[[3,3],[3,4],[4,4]]`


** The Keywords `world`, `rooms`, `current`, and `robot` **

The builtin keyword `world` stands for the set of all points in the world. 
Thus, 
`visit world` is short for visiting any point in the world. You can filter the
world as usual:
`visit world containing item is red` will visit some point, if possible, that contains a red item. Similarly, the keyword `rooms` stands for the predefined set of all rooms. Thus, `visit rooms` will visit any of the rooms.

The keyword `current` evaluates to the point that gives the current position of the robot.
Thus, `if item is circle at current { pick item }` picks an item if there is a circular object
at the current location. Note that if there are multiple objects, the `pick item` can pick any one,
not necessarily the circular one. To pick the circular one, you say `if item is circle at current { pick item is circle }`.

The keyword `robot` gives access to the current state of the robot (i.e., the items carried by the robot).
For example, you say `if robot has item { drop item }` to drop an item if the robot is currently carrying one.

**Looping**

There are three loop constructs
 - `foreach` is used in two ways: looping over set of points, e.g. `foreach point in [[1,1], [1,2]] visit point` or looping over set of areas, e.g. `foreach area in [room1, room2] {visit area; drop item}`. Note that `point` and `area` are fixed looping variables (meaning that `foreach x in [[1,1], [1,2]]` is not in the language)
 - `while`: a loop that executes an action while condition is satisfied. An example is `while robot has item {move left; drop item}` 
 - `repeat`: used for repeating fixed number of times, for example `repeat 3 times drop item`


** Combining areas, filtering based on the items they contain **
  
- `visit room3 containing item is red`
filters the area down to points that contain (one or more) red items
  - Tip: areas can be combined with `or` (union of two areas),  `and` (intersection of two areas), and `minus` (relative complement): `room1 or room2`, `world minus room1`, `{world containing item is blue} and {world containing item is red} `
- `visit world containing item is blue` filters world (all points) and takes only those that have a blue item on it
   - __Tip__: if you want to visit a point that has green items, but doesn't circles, it can be done by `visit {world containing item is green} minus {world containing item is triangle}`. This is not the same as `visit world containing item has color green and not has shape triangle` (that one means visiting a point with an item that is both "green and not triangle".)
- `foreach point in world containing item { visit point; pick item }`
will perform an action on every point in an area
  - `world` is an area consisting of every open point
  - `rooms` is a set of areas consisting of 5 predefined areas - rooms (room1,..., room5)
  - `containing` is an optional filter that can be used with `item`, `item is ...`, etc.
  - `point` is used to refer to the individual points specified by `foreach`
- `foreach area in rooms containing item is red { visit area; drop item }`
will loop through areas
  - A collection of areas can be explicitly written: `[room1, room4]`
- Sometimes there will be multiple ways to interpret a command:
first try `visit [7,4]` and then `pick every item not is red and is green`
  - This could possibly be
  `pick every item not { is red and is green }` or
  `pick every item { not is red } and is green`
  - Use the up and down arrows to choose which one you would like


## Defining New Rules

If you enter a command that the system does yet not recognize, you have the
option of defining what the command means in terms of command that the system
does know. The system includes the new definition in the language, so it is
not just a blind macro expansion.

### Defining by Paraphrasing

Paraphrasing is taking a long or unnatural command and phrasing in a different,
equivalent way.

- It is somewhat awkward to say `repeat 3 times move right`; instead try
entering `move right 3`
  - Now type in the definition `repeat 3 times move right`
  - Accept the action and click "Finish Definition"
  - Not only will the system recognize this command in the future, it will also
recognize similar commands like `move left 2` or `move up 5`
  - __Tip:__ together with the animation, the system will show you what it understood in the core (formal) language below the command bar
- `pick a red or green item`
  - This could be defined as: `pick item is red or is green`
- `visit room1, room2, and room3`
  - This could be defined as: `foreach area in [room1, room2, room3] visit area`
- **Tip**: another way is to first write the definitions (any number of them) and then decided to use a shorter/more usable expression for this (sequence of) command(s). This is achieved by clicking on the number next to the first command of the sequence that needs to be redefined and typing in the expression.
 - __Tip__: If you forgot which commands have been defined so far, you can click the arrow on the right to show the list of definitions (performed by you or the others)

### Defining Abstract Commands

It is also possible to define more abstract or complex commands in terms of
simpler commands.

- `get all red items`: pick up every red item on the map
  - This would be expressed by the much longer command
`foreach point in world containing item is red { visit point; pick every item is red }`
- `bring a blue item to [5,5]`: find a blue item and drop it at the point `[5,5]`
  - `visit world containing item is blue`
  - `pick item is blue`
  - `visit [5,5]`
  - `drop item is blue`
- `sort all red and green items into room4 and room5`: gather all red and green
items and sort them into `room4` and `room5` respectively
  - `get all red items`
  - `get all green items`
  - `visit room4`
  - `drop every item is red`
  - `visit room5`
  - `drop every item is green`

This concludes the basic part of the tutorial. Feel free to play around in the <a href="/#/build" target="_blank">build page</a>.

## Advanced Language Constructs

Feel free to skip this section and reference it as needed.

- `{` and `}` function as optional grouping symbols
  - Group actions as a single action `{ move left; move up}` (these are
completed in the specified sequence)
- `visit [9,8] while avoiding room3`
  - `visit` the specified point without entering the specified area
- An area can also be specified by its corner points
  - `foreach point in area with corners [3,3] and [4,5] { visit point }`
  - If the area spans walls, the walls will not be considered in the area
- `if` statements can be used with `robot has item`, `robot at [3,3]`,
`robot at room2`, `item at [4,4]`, `item at room1`, etc.
  - `if CONDITION ACTION`
  - `if robot has item is red { move down }`

- `if` statements can also be used with the possibility  of an action being
completed (realizability of an action)
  - `if possible ACTION ACTION`
  - `if possible { move left } { move right }`
  - An action is `possible` if every step can be completed successfully
  - `if possible { move left; pick item is green } { move right }`
- Closely related to possibility is strictly completing a sequence of commands
  - `strict { move left ; pick item is red ; drop item is circle }` 
  - If at least one of the actions in sequence is not realizable, the
robot will do nothing; otherwise, the action will be completed normally
- Realizability of primitive actions
  - `visit` is realizable if there is the path from robot's current position to the location specified
  - `pick`/`drop` is realizable if the set specified to be picked/dropped is not empty
  
