From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.

Ltac2 Type trigger_var := 
  [TGoal | TSomeHyp].

Ltac2 Type rec trigger_form := [
  | TTerm (constr)
  | TArr (trigger_form, trigger_form)
  | TAnd (trigger_form, trigger_form)
  | TOr (trigger_form, trigger_form)
  | TTop
  | TBottom
  | TDiscard
  | TMetaVar ].

Ltac2 Type trigger := [
  | TEq (trigger_var, trigger_var)
  | TIs (trigger_var, trigger_form) 
  | TContains (trigger_var, trigger_form)
  ].

Ltac2 rec type_of_hyps (l : (ident * constr option * constr) list) :=
  match l with
    | [] => []
    | (id, opt, ty) :: xs => ty :: type_of_hyps xs
  end.


(* Works only if one goal is under focus *) 

Ltac2 interpret_trigger_var (tv : trigger_var) :=
  match tv with
    | TGoal => let h := Control.hyps () in 
        type_of_hyps h
    | TSomeHyp => let g := Control.goal () in [g]
  end.

Ltac2 interpret_trigger_eq (a : trigger_var) (b : trigger_var) :=
  let l1 := interpret_trigger_var a in
  let l2 := interpret_trigger_var b in
  if List.exist (fun x => List.mem Constr.equal x l1) l2 then Some [] else None.













