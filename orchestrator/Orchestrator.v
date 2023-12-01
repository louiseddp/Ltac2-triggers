From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
Require Import List.
Import ListNotations.
Require Import Printer.
Require Import Triggers.
Require Import Tactics.


(** Test : it is still possible to use tactics defined 
in the [Tactics] file *)
Goal (True /\ True) /\ (True -> True -> True /\ True).
Proof.
run "split" [].
run "split" [].
run "myexact" ['I].
run "myexact" ['I].
intros H1 H2.
run "myapply2" ['H1; 'H2].
Qed.