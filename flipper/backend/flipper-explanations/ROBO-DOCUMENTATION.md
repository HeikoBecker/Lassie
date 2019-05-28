# Robo Specific Documentation

Files are contained under `src/edu/stanford/nlp/sempre/interactive`.
Grammar files are contained under `interactive`. The formal grammar can be
found in [robo.grammar](/interactive/robo.grammar).

## Planner

The `Planner` package contains the class `PathFinder` which is responsible for
planning the motion of the robot. The pathing is done by nondeterministically
selecting an efficient path using A\* (A\* implemented as part of the
[Hipster library](https://github.com/citiususc/hipster)). When visiting
multiple points in a nondeterministic order, the Christofides algorithm is
used as a heuristic to determine an efficient order in which to visit the
points.

## Robolurn Package (final name TBD)

The `Robolurn` package contains classes that directly relate to visual world
that is displayed on the front end. `RoboAction` describes individual actions
the robot can take (e.g., moving one square, picking up/dropping an item)
specifying the specific location and nature of the action.A `WorldBlock` simple
represents a wall or item present in the RoboWorld. `RoboWorld` contains a set
of `WorldBlocks` describing the current state of the world as specified by the
client (SEMPRE receives the world context from the client) and an ordered list
of `RoboAction`s that are converted into JSON in order to be sent to the front
end. This class also contains all logic related to core language functions (e.g.,
`visit`, `pick`, `drop`).

