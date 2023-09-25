Require Import Utils.
Require Import Trigger.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac elim_nat :=
  match goal with
    | H : nat |- _ => clear H
  end.

(** Triggers for tactics **)


Ltac2 trigger_and_intro := TIs TGoal (TAnd TDiscard TDiscard).
Ltac2 trigger_axiom := TIs TGoal (TVar TSomeHyp).
Ltac2 trigger_intro := TIs TGoal (TArr TDiscard TDiscard).
Ltac2 trigger_or_elim := TIs TSomeHyp (TOr TMetaVar TMetaVar).
Ltac2 trigger_left := TIs TGoal (TOr (TVar TSomeHyp) TDiscard).
Ltac2 trigger_right := TIs TGoal (TOr TDiscard (TVar TSomeHyp)).

(** warning : thunk because constrs are only produced at RUNTIME *)
Ltac2 trigger_elim_nat () := TIs TSomeHyp (TType 'Set).

(** Not really expressible **)
Ltac2 trigger_apply_in := TIs TSomeHyp (TArr (TVar TSomeHyp) TDiscard).



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
| ChangesHyp (constr list  -> unit)
| ChangesAll (constr list -> unit)
| ProducesHyp (constr list -> unit)]. 

Ltac2 thunksplit := fun l => apply_ltac1 ltac1val:(split) l.
Ltac2 thunkassumption := fun l => apply_ltac1 ltac1val:(assumption) l.
Ltac2 thunkintro := fun l => apply_ltac1 ltac1val:(intro) l.
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
  (thunkleft, trigger_left, "left");
  (thunkright, trigger_right, "right")].

Print Ltac2 trigs.

Ltac2 run (t : constr list -> unit) (l : constr list) := 
t l.


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
                else run tac (List.map (fun x => constr_quoted_to_constr x) l) ;
            Control.enter (fun () => trigger' init_triggers init_triggers ((message, l)::trig_tac)))
          | None => 
             (Message.print (Message.concat 
             (Message.of_string "The following tactic was not triggered: ") (Message.of_string message)));
             trigger' init_triggers triggers' trig_tac
        end
    end
  in
  trigger' (trigs ()) (trigs ()) triggered_tactics.

(* Tactics with no arguments : 

- either their trigger is not valid after they are called (ex : trakt)
- or the tactic has some fuel (can be applied only a finite number of times)
- or they do not make any progress

*)

(* TODO : optimization + refinement of types of tactics (their action 
on the goal, the hypotheses etc.) + add trakt in it *)

Tactic Notation "orchestrator" := ltac2:(orchestrator ()).

Section tests.

Goal (forall (A B C D : Prop), nat -> A -> B -> C -> D -> (A /\ B /\ C /\ D)).
orchestrator. Qed.

Goal (forall (A B : Prop), A \/ B -> B \/ A).
orchestrator. assumption. Qed.

End tests.

