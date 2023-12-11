Require Import Orchestrator.Triggers.
Require Import Orchestrator.Printer.
Require Import List.
From Ltac2 Require Import Ltac2.
Import ListNotations.

Ltac2 initial_state () :=
  let hyps := Control.hyps () in
  let g := Control.goal () in
  (hyps, Some g).

Ltac2 initial_computed_subterms () :=
  { subterms_coq_goal := ([], None)}.

Ltac2 env_triggers () :=
  { env_triggers := [] }.

Ltac2 test_trigger (t: trigger) :=
  let init := initial_state () in
  let res := interpret_trigger init (env_triggers ()) (initial_computed_subterms ()) t in
  print_interpreted_trigger res.

(** Test De Brujin indexes, eq and anonymous functions **) 

Goal forall (n: nat), (fun x => x) n = n.
intros n.
test_trigger (TContains TGoal Flag_unneeded  (TRel 1)). 
test_trigger (TContains TGoal  Flag_unneeded (TLambda (TTerm 'nat true) tDiscard)).
test_trigger (TContains TGoal Flag_unneeded (TLambda tDiscard (TRel 1))). (* warning: as in 
the kernel, De Brujin indexes start with 1 *)
test_trigger (TIs TGoal Flag_unneeded (TEq (TTerm 'nat true) tDiscard tDiscard)).
let g := Control.goal () in print_closed_subterms g.
Abort.

(** Test match, definitions and fixpoints **)

Goal (length =
fun A : Type =>
fix length (l : list A) : nat := match l with
                                 | [] => 0
                                 | _ :: l' => S (length l')
                                 end).
test_trigger (TContains TGoal Flag_unneeded (TConstant None Flag_type)).
test_trigger (TContains TGoal Flag_unneeded (TConstant (Some "length") Flag_type)).
test_trigger (TContains TGoal Flag_unneeded (TFix tDiscard tDiscard)).
test_trigger (TContains TGoal Flag_unneeded (TFix tDiscard tDiscard)).
test_trigger (TContains TGoal Flag_unneeded (TCase tDiscard tDiscard (Some [TTerm '0 false; tDiscard]))).
Abort.

Goal  (forall A, @length A =
fix length (l : list A) : nat := match l with
                                 | [] => 0
                                 | _ :: l' => S (length l')
                                 end).
Fail test_trigger (TContains TGoal Flag_unneeded (TFix (TAny Flag_term) tDiscard)).
test_trigger (TContains TGoal Flag_unneeded (TFix tDiscard tDiscard)).
Abort.

(* Test named *)

Goal (forall (A B C : Prop), (A /\ B) -> (A /\ B) \/ C).
intros A B C H.
test_trigger (TIs TGoal Flag_unneeded (TOr tDiscard tDiscard)).
test_trigger (TBind (TIs TGoal Flag_unneeded (TOr tArg tDiscard)) ["A"] (TIs (TNamed "A") Flag_unneeded (TAnd (TAny Flag_term) tDiscard))).
Abort.



