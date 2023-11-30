From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
Require Import List.
Import ListNotations.
Require Import Printer.
Require Import Triggers.

Ltac myapply2 A B := split ; [apply A | apply B].

(** Reification of Ltac1 tactics *)

Ltac2 currify (tac : t) (l : t list) :=
  Ltac1.apply tac l run.

Ltac2 constr_to_tacval (l : constr list) :=
  List.map (fun x => of_constr x) l.

Ltac2 apply_ltac1 (tac : t) (l : constr list) := 
currify tac (constr_to_tacval l).

Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

(** [run] runs a Ltac1 tactic *) 

(* Ltac2 run (id : ident) (l : constr list) :=
let tac := ref [ident:(Orchestrator) ; ident:(Tactics); id] in
let l := List.map of_constr l in
let l := of_list l in
ltac1:(tac l |- 
let f := ltac2:(tac l |- 
let l := to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f tac l) tac l.

Ltac2 run2 (tac : t) (l : constr list) :=
let l := List.map of_constr l in
let l := of_list l in
ltac1:(tac l |- 
let f := ltac2:(tac l |- 
let l := to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f tac l) tac l.
 *)
Ltac2 run (tac : t) (l : t) :=
ltac1:(tac l |- 
let x := tac in (** kind of "type cast": transforms [tac] into a tacvalue *)
let f := ltac2:(tac l |- 
let l := to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f x l) tac l.

Ltac2 run_list (tac : t) (l : constr list) :=
let l := List.map of_constr l in
let l := of_list l in
ltac1:(tac l |- 
let x := tac in (** kind of "type cast": transforms [tac] into a tacvalue *)
let f := ltac2:(tac l |- 
let l := to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f x l) tac l.

Ltac myexact t := exact t.

Tactic Notation (at level 0) "run" tactic(tac) "|" constr_list(l) := 
let f := ltac2:(tac l |- run tac l) in f tac l.

Ltac2 run_tacnot l := fun tac => 
let l := List.map of_constr l in
let l := of_list l in
ltac1:(tac l |- let x := tac in run x | l) tac l.


Set Default Proof Mode "Classic".
Section tests. 

Goal (True /\ True) /\ (True -> True -> True /\ True).
Proof.
run split |.
run split |.
run myexact | I.
ltac2:(let x := of_ident ident:(exact) in run_tacnot ['I] x).
run myexact | I.
intros H1 H2.
run myapply2 | H1 H2.
Qed.

End tests.


