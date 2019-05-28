open bossLib realTheory arithmeticTheory;

val _ = new_theory "examples";

Theorem binom1:
  ! (a b:real). (a + b) pow 2 = a pow 2 + 2 * a * b + b pow 2
Proof
  (* TODO *)
QED

Theorem binom2:
  ! (a b:real). (a - b) pow 2 = a pow 2 - 2 * a * b + b pow 2
Proof
  (* TODO *)
QED

Theorem binom3:
  ! (a b:real). (a + b) * (a - b) = a pow 2 - b pow 2
Proof
  (* TODO *)
QED

(*
  Gaussian formula
*)
val sum_def = Define `
  (sum 0 = 0:real) /\
  (sum (SUC n) = (&(SUC n) + sum n))`

Theorem gaussian_sum:
  ! n. (sum n = (((&n):real) * (1 + &n)) / 2)
Proof
  (* TODO *)
QED

(*
  The sum of all n uneven numbers is n^2
*)
val square_number_def = Define `
  (square_number (0:num) = 1:real) /\
  (square_number (SUC n) = ((2:real) * (&(SUC n)) + &1) + square_number n)`

Theorem square_number_is_square:
  ! n. square_number n = (&n+1) * (&n+1)
Proof
  (* TODO *)
QED

val sum_of_cubes_def = Define `
  (sum_of_cubes 0 = 0:real) /\
  (sum_of_cubes (SUC n) = (&(SUC n)) pow 3 + sum_of_cubes n)`;

(**
  The sum of cubed numbers up to n is the squared sum
**)
Theorem sum_of_cubes_is_squared_sum:
  ! n. sum_of_cubes n = (sum n) pow 2
Proof
  (* TODO *)
QED

val SOS2_def = Define `
  (SOS2 0 = 0) /\
  (SOS2 (SUC n) = SUC n * SUC n + SOS2 n)`;

Theorem sos2_3:
  ! n. 3 * (SOS2 n) = ((n * (n+1))*(2 * n + 1)) DIV 2
Proof
  (* TODO *)
QED

val _ = export_theory();
