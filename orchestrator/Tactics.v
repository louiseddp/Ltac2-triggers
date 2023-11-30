From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
Require Import Printer.
Require Import Triggers.

Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

(** The tactics should be saved in a specific file because we need the absolute path **)

Ltac mysplit := split.
Ltac myexact t := exact t.
Ltac myapply2 A B := split ; [apply A | apply B].

(** Reification of Ltac1 tactics **)

Ltac2 currify (tac : t) (l : t list) :=
  Ltac1.apply tac l run.

Ltac2 constr_to_tacval (l : constr list) :=
  List.map (fun x => of_constr x) l.

Ltac2 apply_ltac1 (tac : t) (l : constr list) := 
currify tac (constr_to_tacval l).

Ltac2 run (s : string) (l : constr list) :=
let ident := Ident.of_string s in
let tac := ref [ident:(Orchestrator) ; ident:(Tactics); get_opt ident] in
let l := List.map of_constr l in
let l := of_list l in
ltac1:(tac l |- 
let f := ltac2:(tac l |- 
let l := Ltac1.to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f tac l) tac l.


Goal (True /\ True) /\ (True -> True -> True /\ True).
run "mysplit" [].
run "mysplit" [].
run "myexact" ['I].
run "myexact" ['I].
intros H1 H2.
run "myapply2" ['H1; 'H2]. Qed.


