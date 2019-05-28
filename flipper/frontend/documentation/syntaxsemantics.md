 # Specification language
The language talks about the grid world in which there is a robot and some items of few different colors. Language can express a location - be it a point in the grid, a set of such points (area), or a set of areas (collection). Furthermore, a location can be obtained by filtering a set locations based on the items they contain. Locations can be combined using set operations - union, intersection and difference. Items can be filtered by their properties. One can limit the result of such filtering to a single (nondeterministically chosen) item. Robot can visit a location, pick a filtered set of items from its current position or drop a filtered set of items to its current position. Boolean primitives supported are whether a robot is at particular position or area; if an item is at particular position or area and if robot holds a particular item. Finally, there is a boolean primitive that tells whether an action is realizable.
The language supports simple control-flow structures: if-branching, while loops, iteration over points and areas and repeating an action fixed number of times.



## Syntax
This grammar should help user understanding the core language. The actual implementation is available in the file [robo.grammar](https://gitlab.mpi-sws.org/gavran/sempre-interactive/blob/master/interactive/robo.grammar)

 **Program ( Root )**

   - `Root -> ST`




**Statement (ST)**

 - `ST -> Spec`
 - `ST -> {ST}` *grouping statements, useful in looping or branching*
 - `ST -> ST1; ST2` *ST1 gets executed and once it is finished ST2 gets executed*
 - `ST -> if Sit ST1`  *If Sit evaluates to true, ST1 gets executed*
 - `ST -> while Sit ST1`  *While Sit evaluates to true, ST1 gets executed*
 - `ST -> foreach point in Area ST1` *The loop variable can only be point *
 - `ST -> foreach area in Collection ST1`*The loop variable can only be area*
 - `ST -> repeat n times ST1`


**Locations: Points, Areas, and Collections of areas**

A 2D-grid consists of (x,y)-denoted points. An area is a set of points {(x<sub>1</sub>, y<sub>1</sub>), ..., (x<sub>n</sub>, y<sub>n</sub>)}. A collection of areas is a set of sets of points { {(x<sub>1,1</sub>, y<sub>1,1</sub>),..., (x<sub>1,n</sub>,y<sub>1,n</sub>)},...,{(x<sub>m,1</sub>,y<sub>m,1</sub>),...,(x<sub>m,k</sub>, y<sub>m,k</sub>)}}

  - `Point -> [x1, y1]`
  - `Point -> current` *a current point on which the robot is standing*
  - `Area -> [Point1, Point2,...,PointN]` *a set consisting of fields {(x1,y1),(x2,y2),...,(xn, yn)}*
  - `Area -> world` *area of the whole map*
  - `Area -> Area1 or Area2` *a union of areas Area1 and Area2*
  - `Area -> Area1 and Area2` *an intersection of areas Area1 and Area2*
  - `Area -> Area1 minus Area2` *a difference between areas Area1 and Area2*
  - `Area -> area with corners Point1 and Point2` *an area defined by corners Point1 and Point2*
  - `Area -> Area containing Item` *subarea of Area (consisting of fields that contain an item described by Item)*
  - `Collection -> [Area1, Area2,..., AreaN]` *a set of areas (set of sets of points)*
  - `Collection -> rooms` *collection of all predefined rooms*
  - `Collection -> Collection containing Item` *subcollection of Collection consisting of areas that contain an item as specified by Item*
  - `Location -> Point | Area | Collection`


**Situations (Sit)**


 - `Sit -> Item at Area` *true if at least one item specified by Item is at area A*
 - `Sit -> Item at Point` *true if at least one item specified by Item is at point P*
 - `Sit -> robot has Item` *true if the robot carries at least one item described by Item*
 - `Sit -> robot at Point` *true if the robot is at Point*
 - `Sit -> robot at Area` *true if the robot is at Area (any of the fields)*
 - `Sit -> possible Spec`  *if specification Spec is realizable, return true, otherwise false*
 - `Sit -> Sit and Sit` *logical and*
 - `Sit -> Sit or Sit` *logical or*
 - `Sit -> not Sit` *logical negation*

**Specifications (Spec)**


If a specification is realizable, a controller is synthesized and the spec is executed. If not, it reports unrealizability and asks user to change it/remove it from the program.

  - `Spec -> move Direction` *robot moves one space in the direction `up`, `down`, `right`, or `left`*
  - `Spec -> visit Location while avoiding Area`  *robot should visit Location (Collection, Area or Point) , and while doing this not enter any point of Area \ Location*
  - `Spec -> visit Location`  *syntactic sugar for __visit Location while avoiding $`\emptyset`$__*
  - `Spec -> pick LimitedItem` *pick item(s) defined by item definition I (from your current point). If nothing can be picked, the specification is considered unrealizable*
  - `Spec -> drop LimitedItem` *drop item(s) defined by item definition I that it currently has (it should drop it on its location). If nothing can be dropped, the specification is considered unrealizable*
  - `Spec -> strict Spec` only perform Spec if all actions can be completed (if one action fails, nothing executes)

**Items definitions and item filters**

Item filters function as logical filters. One can say _pick item_ with the meaning pick whatever there is at your current location, or _pick item is blue_ meaning that one should pick whatever there is at current location **only** if it is blue. The item definition is then either a filter (takes everything that passes through the filter) or a single item (nondeterministically chosen) that passes the filter.

  - `LimitedItem -> every Item` _any number of items; set will not be restricted_
  - `LimitedItem -> Item` _set will be restricted to one item_
  - `Item -> item` _no filter, any item matches_
  - `Item -> item Filter` _item with the specified filter_
  - `Filter -> is C | is S` _C is from finite set of colors (resp S is from finite set of shapes), everything that is of color C (of shape S) passes the filter_
  - `Filter -> Filter1 and Filter2`  _a conjunction of two item filters_
  - `Filter -> Filter1 or Filter2` _a disjunction of two item filters_
  - `Filter -> not Filter1` _a negation of an item filter F1_
  - `C -> red | blue | green | yellow`
  - `S -> triangle | square | circle`

## Semantics

Semantics is defined on the following world model

**World Model**

The world and its state are represented by
 - the grid `M = {0,..,w-1}x{0,..,h-1}`
 - the set of obstacle (wall) positions `O ⊆ M`
 - graph `G` build from `M` and `O` that represents connections between positions
 - robot `r` with its position `r.current ∈ M` and the items robot holds given in `r.items ⊆ N x C`
 - the set of items,with their ids, colors and shapes `I ⊆ N x C x S`. For  `i ∈ I` we have `i = (i.id, i.color, i.shape)`. The set of items is a disjoint union of items in the world (`I_w`) and the items that robot holds (`I_r`).
 - mapping `pos : I_w -> M` that maps each item in the world to its position



 There is also a concept of *unrealizability* that refers to statements `ST`. Whenever a statement is unrealizable, it is written explicitly (otherwise, it is considered realizable).


---
**$LimitedItem**
 - |every $Item|                         :: |$Item|
 - |$Item|                              :: nondeterministically chosen `i ∈ |$Item|`
 
 
**$Item**
 - |item $Filter|                         :: `{i ∈ I: Filter(i) == true}`
 
 
 **$Filter**
 - \<is c\>        :: `λi. i.color == c`
 - \<is s\>        :: `λi. i.shape == s`
 -  \<$Filter1  and $Filter2\> :: `<Filter1> ∧ <Filter2>`
 - \<$Filter1 or $Filter2\> :: `<Filter1> ∨ <Filter2>`
 - \<not $Filter\> :: `¬ <Filter>`


---

**Locations**
 - |[x1, y1]| :: `(x1, y1)∈M`
 - |`current`| :: `r.current`
 - |[$Point_1, $Point_2,...,$Point_n]| :: `{|$Point_1|,|$Point_2|,...,|$Point_n|} ⊆ M`
 - |`world`| :: `M`
 - |$Area1 or $Area2| :: `|$Area1| ∪ |$Area2|`
 - |$Area1 and $Area2| :: `|$Area1| ∩ |$Area2|`
 - |$Area1 minus $Area2| :: `|$Area1|  \ |$Area2|`
 - |area with corners $Point1 and $Point2| :: `{ l ∈ M \ O:   $Point1.x ≤ l.x ≤ $Point2.x ∧ $Point1.y ≤ l.y ≤ $Point2.y}`
 - |$Area containing $Item| ::  `|$Area| ∩ {pos(i): i ∈ $Item ∩ I_w}`
 - |[$Area_1, $Area_2,..., $Area_n]| ::  `{|$Area_1|, |$Area_2|,...,|$Area_n|} ⊆ 2^M`
 - |rooms| :: `{room_1, room_2,... room_n}`, where `room_k ⊆ M` is a predefined subset of all points
 - |$Collection containing $Item| ::  `{a ∈ $Collection: ∃ i ∈ |$Item| ∩ I_w. i.position ∈ a}`

---


**Specifications**

  - |visit $Location while avoiding $Area| :: if there is a path in `G` from `r` to `g` (if `$Location` is a point, then `g=$Location`; if it is an area, then `g` is any element of  `$Location`, and if it is a collection of areas, then `g` is any element of any element of`$Location`) that never goes through `l ∈ Area \ g`, then `r.current := g`.  otherwise, action is considered unrealizable

  - |move $Direction| :: `|visit newPos|` where `newPos` is defined by `newPos = r.current + (Direction.x, Direction.y)`, with choices for direction being `up = (0, 1)`, `down = (0,-1)`, `left = (-1,0)`, `right = (1,0)`
  - |pick $LimitedItem|  :: let `itemSet2 = {i ∈ $LimitedItem ∩ I_w: pos(i) == r.current}`. Then, `I_r = I_r ∪ itemSet2` and `I_w = I_w \ itemSet2`. If `itemSet2` is an empty set, the specification is considered unrealizable
  - |drop $LimitedItem| :: let `itemSet2 = LimitedItem ∩ I_r`. Then, `I_w = I_w ∪ itemSet2` and `∀i ∈ itemSet2: pos(i) = r.current`. If `itemSet2` is an empty set, the specification is considered unrealizable
  - |strict $Spec| :: if $Spec is unrealizable, nothing happens (otherwise, `|Spec|`). Note: this command is always considered realizable

---

**Situations**

 - |$Item at $Area| ::   `∃ i ∈ $Item ∩ I_w: pos(i) ∈ $Area `
 - |$Item at $Point| ::  `∃ i ∈ Item ∩ I_w : pos(i) = $Point `
 - |robot has $Item| ::   `∃ i ∈ $Item ∩ I_r`
 - |robot at $Point| ::  `r.current == $Point`
 - |robot at $Area| ::  `r.current ∈ $Area`
 - |possible $Spec| :: if specification `$Spec` is realizable, return true, otherwise false*
 - |$Sit1 and $Sit2| ::  `|$Sit1| ∧ |$Sit2|`
 - |$Sit1 or $Sit2| :: `|$Sit1| ∨ |$Sit2|`
 - |not $Sit| ::`¬ |$Sit|`

---

 -  |{$ST}| :: `|$ST|`
 - |$ST1; $ST2| :: `$ST1` (with semantics `|$ST1|` gets executed and once it is finished `ST2` (with semantics `|$ST2|`) gets executed. If any of the two is unrealizable, the whole command is unrealizable
 - |if $Sit $ST1|  :: If `|$Sit|`, `|$ST|` gets executed (otherwise nothing happens)
 - |while $Sit $ST| ::  While `|Sit|` evaluates to true, `|$ST|`. If in any iteration `$Sit` holds true and `$ST` is unrealizable, the whole command is unrealizable
 - |foreach point in $Area $ST| :: `$ST(p), ∀ p ∈ Area` in an unspecified order. If in any iteration `$ST` is unrealizable, the whole command is unrealizable
 - |foreach area in $Collection $ST| :: `$ST(a), ∀ a ∈ Collection` in an unspecified order. If in any iteration `$ST` is unrealizable, the whole command is unrealizable
 - |repeat n times $ST| ::  `|$ST; $ST; ...; $ST|` (n times). If in any iteration `$ST` is unrealizable, the whole command is unrealizable


