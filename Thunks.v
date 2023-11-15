Require Import Utils.
Require Import Trigger.
Require Import Printer.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac elim_nat :=
  match goal with
    | H : nat |- _ => clear H
  end.

(** Triggers for tactics **)

Ltac2 trigger_and_intro := TIs TGoal (TAnd tDiscard tDiscard).
Ltac2 trigger_and_elim := TIs TSomeHyp (TAnd tDiscard tDiscard). (* FIXME: the argument is 
the hypothesis *) 
Ltac2 trigger_and_elim2 := TIs TSomeHyp (TAnd (TAny true) (TAny true)).
Ltac2 trigger_axiom := TIs TGoal (TVar TSomeHyp FNothing).
Ltac2 trigger_intro := TIs TGoal (TArr (TAny false) (TAny false)).
Ltac2 trigger_or_elim := TIs TSomeHyp (TOr tMetavar tMetavar).
Ltac2 trigger_left := TIs TGoal (TOr (TVar TSomeHyp FNothing) tDiscard).
Ltac2 trigger_right := TIs TGoal (TOr tDiscard (TVar TSomeHyp FNothing)).

(** warning : thunk because constrs are only produced at RUNTIME *)
Ltac2 trigger_elim_nat () := TIs TSomeHyp (TType 'Set false).

(** Not really expressible **)
Ltac2 trigger_apply_in := TIs TSomeHyp (TArr (TVar TSomeHyp FTerm) tDiscard).



(** Reification of Ltac1 tactics **)

Ltac2 currify (tac : Ltac1.t) (l : Ltac1.t list) :=
  Ltac1.apply tac l Ltac1.run.

Ltac2 constr_to_tacval (l : constr list) :=
  List.map (fun x => Ltac1.of_constr x) l.

Lemma or_elim2 (A B C : Prop) : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
intros.
ltac2:(currify ltac1val:(or_elim') (constr_to_tacval ['A; 'B])). Abort.

Ltac2 apply_ltac1 (tac : Ltac1.t) (l : constr list) := 
currify tac (constr_to_tacval l).

(** Thunks **) 

Ltac2 Type Thunk := 
[ ChangesGoal (constr list -> unit)
| ChangesHyps (constr list  -> constr list) (* the changed hypotheses *)
| ChangesAll (constr list -> unit)
| ProducesHyp (constr list -> constr list)]. (* the new hypoteses *) 

Ltac2 thunksplit := fun l => apply_ltac1 ltac1val:(split) l.
Ltac2 thunkassumption := fun l => apply_ltac1 ltac1val:(assumption) l.
Ltac2 thunkintro := fun l => apply_ltac1 ltac1val:(intro) l.
Ltac2 thunkandelim := fun l => apply_ltac1 ltac1val:(and_elim) l.
Ltac2 thunkorelim := fun l => apply_ltac1 ltac1val:(or_elim') l.
Ltac2 thunkleft := fun l => apply_ltac1 ltac1val:(left) l.
Ltac2 thunkright := fun l => apply_ltac1 ltac1val:(right) l.
Ltac2 thunkelimnat := fun l => apply_ltac1 ltac1val:(elim_nat) l.

Ltac2 trigs () :=
  [(thunksplit, trigger_and_intro, "split"); 
   (thunkintro, trigger_intro, "intro");
  (thunkelimnat, trigger_elim_nat (), "elim_nat");
  (thunkassumption, trigger_axiom, "assumption");
  (thunkorelim, trigger_or_elim, "or_elim");
  (thunkandelim, trigger_and_elim2, "and_elim");
  (thunkleft, trigger_left, "left");
  (thunkright, trigger_right, "right")].

Ltac2 thunks () := 
[(thunksplit, "split"); 
(thunkintro, "intro") ; 
(thunkelimnat, "elim_nat");
(thunkassumption, "assumption"); 
(thunkorelim, "or_elim");
(thunkandelim, "and_elim"); 
(thunkleft, "left"); 
(thunkright, "right")].

Ltac2 trigs2 () :=
[(trigger_and_intro);
 (trigger_intro);
 (trigger_elim_nat ());
 (trigger_axiom);
 (trigger_or_elim);
 (trigger_and_elim2);
 (trigger_left);
 (trigger_right)].

Ltac2 run (t : constr list -> unit) (l : constr list) := 
t l.

Ltac2 Type count := { mutable count : int }.

Ltac2 Type state := 
  { mutable state : ((ident * constr option * constr) list)*(constr option) }.

Ltac2 number_of_goals () := 
let c := { count := 0 } in
Control.enter (fun () => c.(count) := Int.add 1 (c.(count))) ; c.(count).

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

(* The name of the tactic triggered + on which hypothesis it should be triggered *)

Ltac2 Type triggered_tactics :=
{ mutable trs : (string*(constr list)) list  }.

Ltac2 triggered_tactics : (string*(constr list)) list := [].

Ltac2 trigger_tac_equal (x: string*(constr list)) (y: string*(constr list)) :=
  match x, y with
    | (s1, l1), (s2, l2) => 
       Bool.and (String.equal s1 s2) (List.equal Constr.equal l1 l2) 
  end.


Ltac2 orchestrator () :=
  let rec trigger' init_triggers t trig_tac :=
    match t with
    | [] => Message.print (Message.of_string "no trigger found")
    | (tac, trig, message) :: triggers' =>
        match interpret_trigger trig with
          | Some l =>
              if Bool.and (Bool.neg (Int.equal (List.length l) 0)) (List.mem trigger_tac_equal (message, l) trig_tac) then 
                Message.print (Message.concat 
                (Message.of_string message) (Message.of_string " was already applied"));
                trigger' init_triggers triggers' trig_tac
              else (Message.print (Message.concat 
                (Message.of_string "Automaticaly applied ") (Message.of_string message));
                if (Int.equal (List.length l) 0) then (* the tactic takes zero arguments *)
                  run tac []
                else run tac l ;
            Control.enter (fun () => trigger' init_triggers init_triggers ((message, l)::trig_tac)))
          | None => 
             (Message.print (Message.concat 
             (Message.of_string "The following tactic was not triggered: ") (Message.of_string message)));
             trigger' init_triggers triggers' trig_tac
        end
    end
  in
  trigger' (trigs ()) (trigs ()) triggered_tactics.

Ltac2 interpret_triggers_ck cg trigs :=
List.map (interpret_trigger_ck cg) trigs.

(* Ltac2 Type triggered_tactics :=
{ mutable trs : (string*(constr list)) list  }.*)

(* Improvement l empty => not in the list of tac already triggered *)
(* optimisation: do not reinterpret triggers when the tactic does nothing *)
Ltac2 rec orchestrator_ck_aux
  cg (* Coq Goal or modified Coq Goal *)
  trigs (* triggers *)
  tacs (* tactics => should have same length as triggers *)
  trigtacs (* triggered tactics, pair between a name and a tactic *) :=
  match trigs, tacs with
    | [], _ :: _ => Utils.fail "you forgot to specify a trigger for a or several tactics"
    | _ :: _, [] => Utils.fail "you have more triggers than tactics"
    | [], [] => ()
    | trig :: trigs', (tac, name) :: tacs' => 
         let it := interpret_trigger_ck (cg.(state)) trig in
         match it with
          | None => let _ := (Message.print (Message.concat 
             (Message.of_string "The following tactic was not triggered: ") (Message.of_string name))) in 
             orchestrator_ck_aux cg trigs' tacs' trigtacs
          | Some l => 
            if Bool.and (Bool.neg (Int.equal (List.length l) 0)) 
              (List.mem trigger_tac_equal (name, l) (trigtacs.(trs))) then 
               let _ := Message.print (Message.concat 
              (Message.of_string name) (Message.of_string " was already applied")) in
              orchestrator_ck_aux cg trigs' tacs' trigtacs
            else 
              (run tac l ;
              Message.print (Message.concat 
              (Message.of_string "Automatically applied ") (Message.of_string name)) ;
              trigtacs.(trs) := (name, l) :: (trigtacs.(trs)) ;
              Control.enter (fun () =>
              let cg' := cg.(state) in
              let (hs1, g1) := cg' in
              let hs2 := Control.hyps () in
              let g2 := Control.goal () in
              let g3 :=
              match g1 with
                | None => None
                | Some g1' => if Constr.equal g1' g2 then None else Some g2 
              end in
              cg.(state) := (diff_hyps hs1 hs2, g3) ;      
              orchestrator_ck_aux cg trigs tacs trigtacs))
        end
  end.

Ltac2 rec orchestrator_ck trigs tacs trigtacs :=
  let g := Control.goal () in
  let hyps := Control.hyps () in
  let cg := { state := (hyps, Some g) } in 
  orchestrator_ck_aux cg trigs tacs trigtacs ; 
  Control.enter (fun () => orchestrator_ck trigs tacs trigtacs).

(* Tactics with no arguments : 

- either their trigger is not valid after they are called (ex : trakt)
- or the tactic has some fuel (can be applied only a finite number of times)
- or they do not make any progress

*)

(* TODO : optimization + refinement of types of tactics (their action 
on the goal, the hypotheses etc.) + add trakt in it *)

Tactic Notation "orchestrator" := ltac2:(orchestrator ()).

Tactic Notation "orchestrator_ck" := ltac2:(orchestrator_ck (trigs2 ()) (thunks ()) {trs := []}).

Section tests.

Goal (forall (A B C D : Prop), nat -> A -> B -> C -> D -> (A /\ B /\ C /\ D)).
Time orchestrator.
(* Finished transaction in 0.015 secs (0.002u,0.012s) (successful) *)
Restart.
Time orchestrator_ck. Qed. 
(* Finished transaction in 0.015 secs (0.006u,0.008s) (successful) *)

Goal (forall (A B : Prop), A \/ B -> B \/ A).
Time orchestrator.
(* Finished transaction in 0.014 secs (0.005u,0.008s) (successful) *)
Restart.
Time orchestrator_ck.
(* Finished transaction in 0.014 secs (0.006u,0.007s) (successful) *)
Qed.

Goal (forall (A B : Prop), A /\ B -> A \/ B).
Time orchestrator.
(* Finished transaction in 0.004 secs (0.004u,0.s) (successful) *)
Restart.
Time orchestrator_ck.
(* Finished transaction in 0.003 secs (0.003u,0.s) (successful) *)
Qed.

End tests.

