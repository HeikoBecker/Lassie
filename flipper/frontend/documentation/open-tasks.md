= Random tasks people should be able to accomplish using the core language

- send robot to room <roomId>
- make robot pick all green boxes from room <roomId>
- make robot pick all red boxes in the building
- make robot bring exactly 5 boxes to room <roomId>
- send robot to make sure that there are exactly 5 green boxes in room <roomId>
- robot should check if there are any boxes on the neighboring fields and move them away
- order robot to move two steps to the left and pick a green box if its there. (If it's not there, it should just stay in place)

= Guiding tasks

- send robot one place to the left
- send robot two places to the left
- send robot 5 places to the left

- make robot explore its neighborhood (visit 8 positions surrounding it)
- make robot explore the neighborhood of every green box

- make robot pick exactly one red box
- make robot pick exactly 3 red boxes
- make robot pick exactly 5 red boxes
- make robot pick exactly 7 red boxes

- make robot pick at most one red box
- make robot pick at most 3 red boxes
- make robot pick at most 5 red boxes
- make robot pick at most 7 red boxes


# Tasks suggested by Rupak and Eva

## simpler
- Pick up all green items 
- find another blue item
- If room5 contains a blue item, visit room5
- Move all items one step to the right
- Move items such that no two items are on top of each other
- Bring all items to an empty room
- Bring all items to a room with a blue item
- Bring all items to a room that does not contain a blue item
- move blue item from room3 next to red item in room2

## complex
- Sort items into rooms: red ones go to room 1, green to room 2, etc
- Queue up all blocks starting at your current location (queue need not be straight)
- Line up all blue items, i.e. put all blue items next to each other, non-overlapping
- make a line of alternate colors
- Line up all items sorted by color. I.e. first all blue items, then all red items, etc.
- Bring all red items to room 1, but never carry more than two things at once
- Go to a room that contains (exactly 1 | at most 2 | at least k) item(s) 
  - *how would I accomplish that?*
- Distribute items such that no two items of the same color share a room
- Put a red item next to every blue item
- Put a blue item right of every red item and left of every green item   (this would required as many blue items as there are of the other colors)
- Move an item to roomX, but do not place it immediately next to a red item
- Patrol indefinitely over fields that contain item

## not sure if possible
- get me or Ivan a red item
- get me a red or green item
- use items to block off access to room 1
- Move every item to the next room, i.e. rotate all items (not sure this is possible, as the rooms are probably not numbered) 
 
