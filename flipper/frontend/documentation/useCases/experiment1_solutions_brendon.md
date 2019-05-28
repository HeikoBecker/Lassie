1
- Get one green square 
- Visit any field containing both a yellow item and a circle-shaped item (may be the same item)
- Pick a yellow item from that space
- If possible, pick a square shaped item (from that space). Else, drop yellow item.

```
def: get green square
	visit world containing item has color green and has shape square
	pick item has color green and has shape square
visit world containing item has color yellow and world containing item has shape circle
def: pick yellow
	pick item has color yellow
if possible pick item has shape square pick item has shape square else drop item has color yellow // This does not work in the system -- do we have an "else" construct?
```

2 // Was I supposed to reset the world here? Because if I do, the robot will have no items
 - Visit empty space
 - Put the items the robot currently holds to different empty spaces on the map
 - Visit any field containing both a triangle-shaped item and a green item (may be the same item) and pick only if these are two different items (one that is green, one that is triangular)
 
```
def: visit empty point
	visit world minus {world containing item}
while possible drop item { visit empty point; drop item }
visit world containing item has color green and has shape triangle; if possible {pick item has color green; pick item has shape triangle} pick item has color green or has shape triangle
```

3
 - Bring all items to room1 
 - Pick exactly 3 red items
 - Build a tower at any field consisting of exactly 2 red, 2 green and 2 blue items.
 
```
def: get every item
	foreach point in world containing item {visit point; pick every item}
visit room1; drop every item
def: pick 3 item has color red
	repeat 3 times pick item has color red
get every item has color green or has color blue
visit empty point
drop 2 item has color red; drop 2 item has color green; drop 2 item has color blue
visit empty point
```

4
 - Get one red triangle
 - Collect all red items
 - Put all blue items in room3
 
```
get red triangle
get every item has color red // The way this generalized, it came up with an unrealizability error but still completed the command successfully
get every item has color blue; visit room3; drop every item has color blue
```

5
 - Put all red items in a line on the floor
 - Pick all green items. Drop all of them to empty places.
 - Make sure that every room has one red or blue item in it. 
 
```
def: get every red item
	get every item has color red
visit room3
while possible drop red item {drop red item; move right}
get every item has color red or has color blue
foreach area in rooms {visit area; drop item has color red or has color blue}
```

6
 - Bring all red items to a room that contains a yellow square
 - Make sure that there is no field that contains only yellow items, but not blue circles.

```
get every item has color red
foreach area in rooms if item has color yellow at area {visit area; drop every red item}
// The second instruction of 6 was difficult to understand
get every yellow item
visit world containing item
drop every yellow item
```

7
 - Make sure that each room contains only items of a single color (you don't have to do it in a general way, step by step is ok)
 - Line up items in lines. Make sure that each color is lined up separately (you don't have to do it in a general way, step by step is ok)
 - If there are (at least) 5 items at room2, distribute them around rooms. Otherwise, bring all items (from the whole map) to room2.
 
```
get every item
foreach area in rooms {visit area; drop item}
get every item
def: move 2 down
	repeat 2 times move down
move 5 left
def: make red line right
	while possible drop item has color red {drop item has color red; move right}
make yellow line down
make blue line left
make green line down
def: get item from room3
	visit room3 containing item
if possible {repeat 5 times {get item from room2}} move right else {get every item; visit room2; drop every item} // Again, the else construct does not work for me, but it is supposed to work?
```
