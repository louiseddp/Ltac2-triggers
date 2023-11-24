Require Import Orchestrator.Triggers.
Require Import Orchestrator.Printer.
Require Import List.
From Ltac2 Require Import Ltac2.
Import ListNotations.

Ltac2 initial_state () :=
  let hyps := Control.hyps () in
  let g := Control.goal () in
  (hyps, Some g).

Ltac2 test_trigger (t: trigger) :=
  let init := initial_state () in
  let res := interpret_trigger init t in
  print_interpreted_trigger res.

(** Test De Brujin indexes, eq and anonymous functions **) 

Goal forall (n: nat), (fun x => x) n = n.
intros n.
test_trigger (TContains TGoal (TRel 1)). 
test_trigger (TContains TGoal (TLambda (TTerm 'nat true) tDiscard)).
test_trigger (TContains TGoal (TLambda tDiscard (TRel 1))). (* warning: as in 
the kernel, De Brujin indexes start with 1 *)
test_trigger (TIs TGoal (TEq (TTerm 'nat true) tDiscard tDiscard)).
let g := Control.goal () in print_closed_subterms g.
Abort.

Print length.
(** Test match, definitions and fixpoints **)

Goal (length =
fun A : Type =>
fix length (l : list A) : nat := match l with
                                 | [] => 0
                                 | _ :: l' => S (length l')
                                 end).
test_trigger (TContains TGoal (TConstant None Flag_type)).
test_trigger (TContains TGoal (TFix tDiscard tDiscard)).
test_trigger (TContains TGoal (TFix tDiscard tDiscard)).
test_trigger (TContains TGoal (TCase tDiscard tDiscard (Some [TTerm '0 false; tDiscard]))).
Abort.

Goal  (forall A, @length A =
fix length (l : list A) : nat := match l with
                                 | [] => 0
                                 | _ :: l' => S (length l')
                                 end).
Fail test_trigger (TContains TGoal (TFix (TAny Flag_term) tDiscard)).
test_trigger (TContains TGoal (TFix tDiscard tDiscard)).
Abort.

