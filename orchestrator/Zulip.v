From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.

Goal True.
let id := ident:(easy) in
let tac := ref [ident:(Coq) ; ident:(Init); ident:(Tactics); id] in
Ltac1.apply tac [] run.
Restart.
Fail let id := ident:(easy) in
let tac := of_ident id in 
Ltac1.apply tac [] run. 
(* Variable F should be bound to a tactic. *)
Ltac1.apply ltac1val:(easy) [] run.
Restart.
Fail let id := ident:(easy) in
let tac := of_ident id in 
Ltac1.apply ltac1val:(tac) [] run. 
(* The reference tac was not found in the current environment. *)
Fail let id := ident:(easy) in
let tac := of_ident id in 
Ltac1.apply (ltac1val:(tac |- tac) tac) [] run. 
(* Expression does not evaluate to a tactic (got a ident). *)
Abort.