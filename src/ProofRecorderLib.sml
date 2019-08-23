structure ProofRecorder =
struct

  open proofManagerLib;

  type 'a stack = 'a list;

  datatype Proof =
    Subgoal of Proof stack
    | Step of string
    | End of int;

  exception GoalRecorderException of string;

  val currProof = ref (Subgoal []);
  val finished :Proof list ref = ref ([]);

  fun reset () = (currProof := Subgoal []; finished := []);

  fun pushStep s curr =
    case curr of
    Subgoal [] => Subgoal [s]
    | Subgoal stk =>
      (let val r = pushStep s (hd stk) in
        Subgoal (r:: tl(stk))
      end
      handle GoalRecorderException _ => Subgoal (s::stk))
    | _ =>  raise GoalRecorderException "Illegal state reached, cannot record step";

  fun pushStepList sl curr =
    case curr of
    Subgoal [] => Subgoal sl
    | Subgoal stk =>
      (let val r = pushStepList sl (hd stk) in
        Subgoal (r:: tl(stk))
      end
      handle GoalRecorderException _ => Subgoal (sl @ stk))
    | _ => raise GoalRecorderException "Illegal state reached, cannot record step";

  fun pushSubgoals n currPrf =
    let
      fun mklist n = if n = 0 then [] else (Subgoal []) :: mklist (n-1);
    in
      pushStepList (mklist n) currPrf
    end;

  fun popStep curr =
    case curr of
      Subgoal [] => raise GoalRecorderException "Removing step from empty record"
    | Subgoal stk =>
      (let
        val (r, res) = popStep (hd stk) in (r, Subgoal (res:: tl(stk))) end
      handle GoalRecorderException s => (hd stk, Subgoal (tl stk)))
    | _ => raise GoalRecorderException "Cannot remove step";

  fun popSubgoal curr =
    case curr of
      Subgoal [] => (curr, NONE)
    | Subgoal stk =>
      (let val (r, res) = popSubgoal (hd stk) in
        case res of
        NONE => (r, SOME (Subgoal (tl stk)))
        | SOME res => (r, SOME (Subgoal (res :: (tl stk))))
      end
      handle GoalRecorderException _ => (Subgoal stk, NONE))
    | _ => raise GoalRecorderException "Cannot remove subgoal";

  fun popMulti n curr =
    if (n = 0) then ([], curr)
    else
      let
        val (s, stk) = popStep curr
        val (steps, stkRem) = popMulti (n-1) stk
      in
        (s::steps, stkRem)
      end;

  fun peek stk =
    case stk of
    Subgoal [] => stk
    | Subgoal stk => peek (hd stk)
    | v => v;

  fun removeN n ls =
    if n = 0 then []
    else case ls of [] => []
      | x :: ls => x::(removeN (n-1) ls);

  fun numTacsBefore stk =
    case stk of
    Subgoal stk =>
        (numTacsBefore (hd stk)
        handle GoalRecorderException _ =>
          (List.length stk))
    | _ => raise GoalRecorderException "Cannot count number of tactics";

  fun closeProofs n =
    if n = 0 then ()
    else
      let
        val (step, stko) = popSubgoal (! currProof);
        val _ = (finished := step :: (! finished));
        val _ = case stko of NONE => () | SOME stk => (currProof := stk);
        val theHd = peek (! currProof)
      in
        case theHd of
        End n =>
          (let val (endStp, stk) = popStep (!currProof)
               val _ = (currProof := stk)
               val steps = removeN n (! finished)
               val _ = (finished := (List.drop (!finished, n)))
               val (prevSteps, nCurr) = popMulti (numTacsBefore (! currProof)) (! currProof)
               val _ = (currProof := (case (snd (popSubgoal nCurr)) of NONE => Subgoal [] | SOME stk => stk))
            in
              finished := ((Subgoal (List.rev prevSteps @ steps)) :: !finished)
          end)
        | _ => ()
      end;

  fun app (t:tactic) (s:string) =
    let
      val numGoalsBefore = List.length (top_goals());
      val _ = e t;
      val numGoalsAfter = (List.length (top_goals()) handle HOL_ERR _ => 0);
      val diff = numGoalsAfter - numGoalsBefore;
      val _ = (currProof := pushStep (Step s) (! currProof))
    in
      if (Int.< (diff, 0)) (* a goal has been closed by t *)
      then closeProofs (~diff)
      else if (Int.> (diff, 0))
      then (currProof := pushSubgoals (diff+1) (pushStep (End (diff+1)) (! currProof)))
      else ()
    end;

  fun pp_finished_rec i fst sl=
    let
      fun tab i = if i = 0 then "" else "  "^(tab (i-1));
    in
    case sl of
    Subgoal stk =>
      if (Int.> (List.length stk, 1))
      then
        (tab i) ^ ">- (\n" ^
          (pp_finished_rec (i+1) true) (hd stk) ^ "\n" ^
          (List.foldr (fn (x,y) => x ^ "\n" ^ y) "" (map (pp_finished_rec (i+1) false) (tl stk))) ^
          " )"
      else
        (tab i) ^ ">- (\n" ^ (pp_finished_rec (i+1) true) (hd stk) ^ " )"
    | Step s => (tab i)^ (if (not fst) then "\\\\ " else "")^ s
    | End _ => ""
    end;

  fun pp_finished sl =
    case sl of
    Subgoal stk =>
      if (Int.> (List.length stk, 1))
      then
        (pp_finished_rec 0) true (hd stk) ^ "\n" ^
        List.foldr (fn (x,y) => x ^ "\n" ^ y) "" (map (pp_finished_rec 0 false) (tl stk))
      else
        (pp_finished_rec 0 true) (hd stk)
    | Step s => s
    | _ => "";

end

(** SIMPLE END_TO_END TEST **)

g `! x y. x < y ==> T`;

app (rpt strip_tac) ("rpt strip_tac");

app (Cases_on `x`) ("Cases_on `x`");

app (cheat) ("cheat");

(** TESTS:
val ts = Step "test";

val stk = pushStep ts (! currProof);
val stkNew = pushStep ts stk;
val stkEnd = (pushStep (End 2) stkNew);
val stkNew2 = pushSubgoals 2 stkEnd;
val _ = (currProof := stkNew2);
val _ = (currProof := pushStep (Step "cheat") (! currProof));

val t = popSubgoal (! currProof);

val stkNew3 = closeProofs 1;

 OLD CODE

  local
    fun numGoals (x:unit) :int = List.length (top_goals());
    fun recordTactic (txt:string) =
      case ! currProof of
      GOAL steps => currProof := GOAL ((STEP txt) :: steps)
      (* FIXME: Maybe print error for invariant violation? *)
      | STEP str => currProof := GOAL [STEP txt, STEP str];
    fun addSubgoals diff =
      if (diff = 0) then ()
      else if (diff < 0)
      then raise GoalRecorderException "Trying to record negative number of goals"
      else
        case ! currProof of
        GOAL steps => (currProof := GOAL ((GOAL [])::steps); addSubgoals (diff-1))
        | STEP str => raise GoalRecorderException
                      "Invariant broken; top recorder goal not a list"
    fun finishCurrGoal () =
      case ! currProof of
      GOAL (GOAL steps :: addSteps) =>
        finishedProof := (* TODO *) (GOAL [])
      | GOAL steps =>
        finishedProof := (* TODO *) (GOAL [])
      | STEP str =>
        raise GoalRecorderException
          "Invariant broekn; top recorder goal not a list";
  in
    (**
      This function is used to both apply the tactic
      t and record txt as its string representation.
      The general assumption is that txt is the string
      equivalent of t because it will be recorded for
      later printing.
    **)
    fun e (t:tactic) (txt:string) =
      let
        (* record size of goal list before applying
           tactic to know how many subgoals must be
           appended to representation *)
        val numOldGoals = numGoals();
        (* apply tactic *)
        val _ = proofManagerLib.e t
        (* record?? tactic *)
        val _ = recordTactic txt;
        val numNewGoals = numGoals();
      in
        (* store new tree *)
        if (numOldGoals = numNewGoals)
        then ()
        else
          let val diff = numNewGoals - numOldGoals in
            if (numOldGoals < numNewGoals)
            then addSubGoals diff
            (* numOldGoals > numNewGoals *)
            else if (diff < ~1)
              then raise GoalRecorderException
                "Tactic solved more goals than it was supposed to"
              else finishCurrGoal()
          end
        end
  end;
**)
