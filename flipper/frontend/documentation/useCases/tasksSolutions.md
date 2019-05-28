This experiment is described in issue #41. There are 2 kinds of solutions provided - the most general ones and some that take advantage of the current map (by seeing where is - for example- an empty space and then using it rather than describing what empty means in the language).


1.
- Get one green square
 - `get green square == visit world containing item has color green and has shape square; pick item has color green and has shape square`
 - `repeat 5 times move right; pick item has color green and has shape square`
- Visit any field containing both a yellow item and a circle-shaped item (may be the same item)
   - `visit has color yellow and has shape square == visit {world containing item has color yellow} and {world containing item has shape square}`
   - `visit {world containing item has color yellow} and {world containing item has shape square}`
- Pick a yellow item from that space
 - `pick yellow == pick item has color yellow`
- If possible, pick a square shaped item (from that space). Else, drop yellow item.
 - `if {pick item has shape square} else {drop item has color yellow} == if possible { pick item has shape square } pick item has shape square ; if not possible { pick item has shape square } drop item has color yellow`
 - `drop item has color yellow`



2.

 - Visit empty space
  - `visit empty == visit world minus {world containing item}`
  - `<nothing>` (because robot is already at empty spot)
 - Get one green circle, one red triangle and one yellow square. Put those items to different empty spaces on the map
  - `get green circle; get red triangle; get yellow square; while robot has item {visit empty; drop item}`
  - `get green circle; get green triangle; get yellow square; repeat 3 times {move left; drop item}`
 - Visit any field containing both a triangle-shaped item and a green item (may be the same item) and pick only if these are two different items (one that is green, one that is triangular)
  - `visit field has green and has triangle == visit {world containing item has color green} and {world containing item has shape triangle}; ` and then `strict {pick item has color  green; pick item has shape triangle}`



3.
 - Bring all items to room1
  - `bring all to room1 == foreach point in world containing item {visit point; pick every item}; visit room1; drop every item`
 - Pick exactly 3 red items
  - `pick 3 red == repeat 3 times {pick item has color red}`
 - Build a tower at any field consisting of exactly 2 red, 2 green and 2 blue items.
   - `get green = visit world containing item has color green; pick item has color green` and then `drop every item; repeat 2 times {get red; get blue; get green}; visit empty; drop every item`
   - `drop item; pick 2 green; pick 2 blue; visit empty; drop every item`


 4.
 - Get one red triangle
  - `get red triangle`
 - Collect all red items
  - `collect red == foreach point in world containing item has color red {visit point; pick every item has color red}`
  - `foreach point in world containing item has color red {visit point; pick item has color red}`
 - Put all blue items to room3`
  - `put blue to room3 == collect blue; visit room3; drop every item has color blue`


5.
 - Put all red items in a line on the floor
  - `line red == collect red; while robot has item has color red {move right; drop item has color red}`  this could be done in a more general way (how do we know that the robot will be able to move right enough times), but this is a satisfactory solution for the experiment
 - Pick all green items. Drop all of them to empty places.
  - `collect green; while robot has item has color green {visit empty; drop item}`
  - `collect green; repeat 3 times {move left; drop item}`
 - Make sure that every room has one red or blue item in it.
  - `drop every item; collect red; collect blue; foreach area in rooms {visit area; drop item}`

6.
 - Build towers of different colors at locations [0,0], [1,1], [3,4] and [5,8]
   - `put green to [0,0] == collect green; visit [0,0]; drop every item has color green` and then `put blue to [1,1]; put yellow to [3,4]; put red to [5,8]` 

7.
 - Bring all red items to a room that contains a yellow square
  - `collect red; visit world containing item has color yellow and has shape square; drop every item has color red`
 - Make sure that each room contains only items of a single color
  - `foreach point in world containing item {visit point; pick every item}; put red to room1; put blue to room2; put green to room3; put yellow to room4`
 - Line up items of red, yellow and blue color in lines.
  - `line red; line blue; line yellow`
