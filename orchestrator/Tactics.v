From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
Require Import Printer.
Require Import Triggers.

(** The tactics should be saved in a specific file because 
[Ltac1.ref] needs the absolute path *)

Ltac mysplit := split.
Ltac myexact t := exact t.
Ltac myapply2 A B := split ; [apply A | apply B].

Tactic Notation "mysplit2" := mysplit.

(** Reification of Ltac1 tactics *)

Ltac2 currify (tac : t) (l : t list) :=
  Ltac1.apply tac l run.

Ltac2 constr_to_tacval (l : constr list) :=
  List.map (fun x => of_constr x) l.

Ltac2 apply_ltac1 (tac : t) (l : constr list) := 
currify tac (constr_to_tacval l).

Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

(** [run] runs a Ltac1 tactic *) 

Ltac2 run (id : ident) (l : constr list) :=
let tac := ref [ident:(Orchestrator) ; ident:(Tactics); id] in
let l := List.map of_constr l in
let l := of_list l in
ltac1:(tac l |- 
let f := ltac2:(tac l |- 
let l := to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f tac l) tac l.

(* Ltac2 run (tac : t) (l : constr list) :=
let l := List.map of_constr l in
let l := of_list l in
ltac1:(tac l |- 
let f := ltac2:(tac l |- 
let l := to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f tac l) tac l.

Ltac2 Notation "run" tac(tactic) := run ltac1val:(tac).
 *)
(* Ltac2 run_ltac1val2 (tac : t) (l : t) :=
ltac1:(tac l |- 
let f := ltac2:(tac l |- 
let l := to_list l in 
let l := get_opt l in
let l := List.map (fun x => get_opt (to_constr x)) l in
apply_ltac1 tac l) in f tac l) tac l.

Tactic Notation (at level 0) "run" ltac(tac) "with" hyp_list(l) := 
idtac 1 ;
let f :=
ltac2:(tac l |- 
run_ltac1val2 (ltac1val:(tac |- tac) tac) l) in 
f ltac:(tac) constr:(l). *)


Section tests. 

Goal (True /\ True) /\ (True -> True -> True /\ True).
Proof.
run @mysplit [].
run @mysplit [].
(* run @mysplit2 []. Uncatchable exception: ref does not work with Tactic Notation *)
run @myexact ['I].
run @myexact ['I].
intros H1 H2. 
run @myapply2 ['H1; 'H2]. Qed.

End tests.


