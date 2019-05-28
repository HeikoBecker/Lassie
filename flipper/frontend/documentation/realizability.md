# Realizability

This document contains the formal definitions of realizable actions in the
robot world. Each definition contains a set of preconditions, constraints,
and postconditions that must be met for the action to be considered "realizable."

By default, an action that is not realizable will not execute (i.e., no partial
execution); when qualifying actions with `strict`, if one action fails, none
of the actions will execute. For example, `strict { A ; B ; C }` means that
if any of the three actions fail, none of the others will execute.

- `visit FIELD`
    ```
    preconditions:
      none

    constraints:
      none

    postconditions:
      robot at FIELD
    ```
- `visit FIELD while avoiding AREA`
    ```
    preconditions:
      none

    constraints:
      AREA is treated as if the contained fields were walls

    postconditions:
      robot at FIELD
    ```
- `pick item FILTER`
    ```
    preconditions:
      robot has N items passing FILTER

    constraints:
      none

    postconditions:
      robot has N + 1 items passing FILTER
    ```
- `pick every item FILTER`
    ```
    preconditions:
      none

    constraints:
      none

    postconditions:
      robot has more than N items passing FILTER
    ```
- `drop item FILTER`
    ```
    preconditions:
      robot has N items passing FILTER

    constraints:
      none

    postconditions:
      robot has N - 1 items passing FILTER
    ```
- `drop every item FILTER`
    ```
    preconditions:
      none

    constraints:
      none

    postconditions:
      robot has less than N items passing FILTER
    ```
