Require Import Trigger.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

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

Ltac2 trigs () :=
  [(thunksplit, trigger_and_intro, "split"); 
   (thunkintro, trigger_intro, "intro");
  (thunkassumption, trigger_axiom, "assumption");
  (thunkorelim, trigger_or_elim, "or_elim");
  (thunkleft, trigger_left, "left");
  (thunkright, trigger_right, "right")].

Print Ltac2 trigs.

(* Record poly := mk {A : Type; e : A}.

Ltac titi := constr:(mk (unit -> unit -> True) ltac:(split)).
Set Default Proof Mode "Classic".

Goal True /\ True.
let x:= titi in idtac x.
match titi with
| {|A:= ?t ; e:= ltac:(t') |} => idtac t'
end.


Ltac2 tactics () := '(mk (unit -> unit) ltac2:(thunksplit)).
Ltac2 tactics () := ['(mk (unit -> unit) ltac2:(thunksplit));
                     '(mk (list Ltac2.constr -> unit) ltac2:(thunkorelim))].

Ltac2 toto := let (_, t) := constr:(tactics ()) in t (). *)

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

Goal (forall (A B C D : Prop), A -> B -> C -> D -> (A /\ B /\ C /\ D)).
orchestrator. Qed.

Goal (forall (A B : Prop), A \/ B -> B \/ A).
orchestrator. assumption. Qed.

End tests.

