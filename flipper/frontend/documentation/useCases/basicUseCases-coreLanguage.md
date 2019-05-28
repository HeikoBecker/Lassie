# Use Cases Expressed in the Core Language

### Basic Use Cases

Here are a selection of the basic use cases expressed in the core language.

- Gather [all] red boxes [here]
  - By "here" we will assume the original current location of the robot `CL`
```
foreach L in world do (
  if (has red at L) then (
    visit L;
    pick all has red
  )
);
visit CL;
drop all
```

- Move all but one box in room A to room B
  - Assume that `A` and `B` are bounded spreads
```
foreach L in A do (
  if (at L) then (
    visit L;
    pick all
  )
);
drop single;
visit B;
drop all
```

- Put all green boxes in room A and all blue boxes in room Y
```
foreach L in world do (
  if (has green at L) then (
    visit L;
    pick all has green
  )
  if (has blue at L) then (
    visit L;
    pick all has blue
  )
);
visit A;
drop all has green;
visit Y;
drop all has blue
```
