From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Printf.
Require Import List.
Import ListNotations.
Require Import Printer.
Require Import Triggers.
Require Import Tactics.

Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 Type cgstate := 
  { mutable cgstate : ((ident * constr option * constr) list)*(constr option) }.

Ltac2 Type triggered_tacs :=
  { mutable triggered_tacs : (string * constr list) list }.

(** Equalities between already triggered tactics of type (string*constr list)
and between two hypotheses *)

Ltac2 already_triggered_equal 
(t1 : string * (constr list)) (t2 : string * (constr list)) :=
  let (s1, l1) := t1 in
  let (s2, l2) := t2 in
  Bool.and (String.equal s1 s2) (List.equal equal l1 l2).

Ltac2 hyp_equal h h' :=
let (id1, opt1, c1) := h in
let (id2, opt2, c2) := h' in
if Ident.equal id1 id2 then
  if Constr.equal c1 c2 then
    match opt1, opt2 with
      | Some x, Some y => Constr.equal x y
      | None, Some _ => false
      | Some _, None => false
      | None, None => true
    end
  else false
else false.

Ltac2 rec diff_hyps hs1 hs2 :=
  match hs1, hs2 with
    | [], hs2' => hs2'
    | x :: xs, y :: ys => 
      if hyp_equal x y then diff_hyps xs ys 
      else y :: diff_hyps xs ys
    | x :: xs, [] => [] (* we do not consider removed hypotheses *)
  end.


(* Ltac2 Type subterms_coq_goal := { mutable subs : (ident*constr list) list * (constr list) option }.
Defined in Triggers.v file *)


(** The Orchestrator uses three states: 
  - the hypotheses and the goal changed by the application of a previous tactic (or the initial goal)
  - the subterms of a term (goal or hypothesis) already computed 
  - the (non absolute) name of the tactics already triggered, with its arguments
(warning: the tactics taking no arguments are NEVER considered as already triggered) *)  

(* Improvement l empty => not in the list of tac already triggered *)
(* optimisation: do not reinterpret triggers when the tactic does nothing *)
Ltac2 rec orchestrator_aux
  cg (* Coq Goal or modified Coq Goal *)
  scg (* Subterms already computed in the proof state *)
  trigs (* Triggers *)
  tacs (* Tactics (as strings, should have same length as triggers) *)
  trigtacs (* Triggered tactics, pair between a string and a list of arguments *) :=
  match trigs, tacs with
    | [], _ :: _ => fail "you forgot have more tactics than triggers"
    | _ :: _, [] => fail "you have more triggers than tactics"
    | [], [] => ()
    | trig :: trigs', (tac, name) :: tacs' => 
         let it := interpret_trigger (cg.(cgstate)) scg trig in
         let _ := print_interpreted_trigger it in 
         match it with
          | None => let _ := printf "The following tactic was not triggered: %s" name  in 
             orchestrator_aux cg scg trigs' tacs' trigtacs
          | Some l => 
            if Bool.and (Bool.neg (Int.equal (List.length l) 0)) 
              (List.mem already_triggered_equal (name, l) (trigtacs.(triggered_tacs))) then 
               let _ := printf "%s was already applied" name in
              orchestrator_aux cg scg trigs' tacs' trigtacs
            else 
              (run tac l ;
              let _ := printf "Automatically applied %s" name in 
              trigtacs.(triggered_tacs) := (name, l) :: (trigtacs.(triggered_tacs)) ;
              Control.enter (fun () =>
              let cg' := cg.(cgstate) in
              let (hs1, g1) := cg' in
              let hs2 := Control.hyps () in
              let g2 := Control.goal () in
              let g3 :=
              match g1 with
                | None => None
                | Some g1' => if Constr.equal g1' g2 then None else Some g2 
              end in
              cg.(cgstate) := (diff_hyps hs1 hs2, g3) ;     
              orchestrator_aux cg scg trigs tacs trigtacs))
        end
  end.

Ltac2 rec orchestrator n trigs tacs trigtacs :=
  if Int.equal n 0 then () else
  let g := Control.goal () in
  let hyps := Control.hyps () in
  let cg := { cgstate := (hyps, Some g) } in 
  let scg := { subterms_coq_goal := ([], None) } in
  orchestrator_aux cg scg trigs tacs trigtacs ; 
  Control.enter (fun () => orchestrator (Int.sub n 1) trigs tacs trigtacs).


