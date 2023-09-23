From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Set Default Proof Mode "Classic".

(** Or elim **)

Lemma or_elim (A B C : Prop) : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
intros Hor HA HB.
destruct Hor as [HorA | HorB].
  * apply HA. assumption.
  * apply HB. assumption.
Qed.

Ltac2 or_elim (a : constr) (b : constr) := apply or_elim with (A := $a) (B := $b).

Ltac or_elim' A B := apply or_elim with (A := A) (B := B).

Lemma test_or_elim (A B C : Prop) : A \/ B -> A \/ B \/ C.
Proof.
intros Hor.
or_elim' A B. 
  * assumption.
  * intro Ha. left. assumption.
  * intro Hb. right. left. assumption.
Qed.

(** Utilities **)

Ltac2 third_arg_equal (x : 'a*'b*'c) (y : 'a*'b*'c) (eq : 'c -> 'c -> bool) :=
  match x, y with
    | (_, _, u1), (_, _, u2) => eq u1 u2
  end.

Ltac2 rec type_of_hyps (l : (ident * constr option * constr) list) :=
  match l with
    | [] => []
    | (id, opt, ty) :: xs => ty :: type_of_hyps xs
  end.

Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 rec flatten_option_list (l : 'a list) :=
  match l with
    | [] => None
    | None :: xs => flatten_option_list xs
    | Some x :: xs => Some x
  end.

Ltac2 is_top (c : constr) :=
  equal c 'True.

Ltac2 is_bottom (c: constr) :=
  equal c 'False.

(* we ignore completely the quantifiers, as our tactics 
are not supposed to work for a logic with them *) 

Ltac2 is_arrow (c: constr) :=
  match Unsafe.kind c with
    | Unsafe.Prod b c => true
    | _ => false
  end.

Ltac2 split_arrow (c: constr) :=
  match Unsafe.kind c with
    | Unsafe.Prod b c => (Binder.type b, c)
    | _ => fail "Should not happen, the input should be a product"
  end.

Ltac2 is_and (c: constr) :=
  match Unsafe.kind c with
    | Unsafe.App c' a => equal c' 'and
    | _ => false
  end.

Ltac2 split_and_or (c: constr) :=
  match Unsafe.kind c with
    | Unsafe.App c' a => (Array.get a 0, Array.get a 1)
    | _ => fail "Should not happen, the input should be a conjunction
  or a disjunction"
  end.

Ltac2 is_or (c: constr) :=
  match Unsafe.kind c with
    | Unsafe.App c' a => equal c' 'or
    | _ => false
  end.


(** Quote and unquote **)

Ltac2 Type rec constr_quoted := [
  | Term (constr)
  | Arrow (constr_quoted, constr_quoted)
  | And (constr_quoted, constr_quoted)
  | Or (constr_quoted, constr_quoted)
  | Top 
  | Bottom].

Ltac2 rec constr_to_constr_quoted (c : constr) :=
  if is_top c then Top
  else if is_bottom c then Bottom
  else if is_arrow c then 
    let (c1, c2) := split_arrow c in 
    Arrow (constr_to_constr_quoted c1) (constr_to_constr_quoted c2)
  else if is_or c then
    let (c1, c2) := split_and_or c in 
    Or (constr_to_constr_quoted c1) (constr_to_constr_quoted c2)
  else if is_and c then
    let (c1, c2) := split_and_or c in 
    And (constr_to_constr_quoted c1) (constr_to_constr_quoted c2)
  else Term c.

Ltac2 rec constr_quoted_to_constr (c: constr_quoted) :=
  match c with
    | Term c' => c'
    | Arrow c1 c2 => 
      let c1' := constr_quoted_to_constr c1 in
      let c2' := constr_quoted_to_constr c2 in 
      Unsafe.make (Unsafe.Prod (Binder.make None c1') c2')
    | Or c1 c2 =>
      let c1' := constr_quoted_to_constr c1 in
      let c2' := constr_quoted_to_constr c2 in 
      Unsafe.make (Unsafe.App 'or (Array.of_list [c1'; c2']))
    | And c1 c2 =>
      let c1' := constr_quoted_to_constr c1 in
      let c2' := constr_quoted_to_constr c2 in 
      Unsafe.make (Unsafe.App 'and (Array.of_list [c1'; c2']))
    | Top => 'True
    | Bottom => 'False
  end.

(** Triggers **)

Ltac2 Type trigger_var := 
  [TGoal | TSomeHyp].

Ltac2 Type rec trigger_form := [
  | TTerm (constr)
  | TVar (trigger_var)
  | TArr (trigger_form, trigger_form)
  | TAnd (trigger_form, trigger_form)
  | TOr (trigger_form, trigger_form)
  | TTop
  | TBottom
  | TDiscard
  | TMetaVar ].

Ltac2 Type rec trigger := [
  | TIs (trigger_var, trigger_form) 
  | TContains (trigger_var, trigger_form)
  | TConj (trigger, trigger) (* two triggers need to be present at the same time *)
  | TDisj (trigger, trigger) (* one of the two triggers needs to be present *)
  ].

(** Interpretation **)

(* Works only if one goal is under focus *) 

Ltac2 interpret_trigger_var (tv : trigger_var) :=
  match tv with
    | TSomeHyp => let h := Control.hyps () in 
        type_of_hyps h
    | TGoal => let g := Control.goal () in [g]
  end.

Ltac2 rec interpret_constr_with_trigger_form 
  (c : constr_quoted) (tf : trigger_form) :=
  match c, tf with
    | Top, TTop => Some [] 
    | Bottom, TBottom => Some []
    | Term c, TTerm c' => if equal c c' then Some [] else None
    | Term c, TVar v => 
       let tv := interpret_trigger_var v in
       if List.mem equal c tv then Some [] else None
    | Arrow c1 c2, TArr tf1 tf2 => 
      let o1 := interpret_constr_with_trigger_form c1 tf1 in
      let o2 := interpret_constr_with_trigger_form c2 tf2 in
        match o1, o2 with
          | Some l1, Some l2 => Some (List.append l1 l2)
          | _ => None
        end
    | And c1 c2, TAnd tf1 tf2 =>
      let o1 := interpret_constr_with_trigger_form c1 tf1 in
      let o2 := interpret_constr_with_trigger_form c2 tf2 in
        match o1, o2 with
          | Some l1, Some l2 => Some (List.append l1 l2)
          | _ => None
        end
    | Or c1 c2, TOr tf1 tf2 => 
      let o1 := interpret_constr_with_trigger_form c1 tf1 in
      let o2 := interpret_constr_with_trigger_form c2 tf2 in
        match o1, o2 with
          | Some l1, Some l2 => Some (List.append l1 l2)
          | _ => None
        end
    | _, TMetaVar => Some [c]
    | _, TDiscard => Some []
    | _ => None
  end. 

Ltac2 interpret_trigger_is a b := 
  let a' := interpret_trigger_var a in
  let result := List.map (fun x => let x' := constr_to_constr_quoted x in 
    interpret_constr_with_trigger_form x' b) a' in
  flatten_option_list result.

Ltac2 interpret_trigger_contains_aux (c : constr) (tf : trigger_form) :=
  let cquote := constr_to_constr_quoted c in
  let rec tac_aux cquote tf :=
  match interpret_constr_with_trigger_form cquote tf with
    | Some success => Some success 
    | None => 
      match cquote with
        | Arrow c1 c2 | And c1 c2 | Or c1 c2 => 
          match tac_aux c1 tf with
            | None => tac_aux c2 tf
            | Some success' => Some success'
          end
        | _ => None
      end  
    end 
    in tac_aux cquote tf.

Ltac2 interpret_trigger_contains (tv : trigger_var) (tf: trigger_form) :=
  let a := interpret_trigger_var tv in 
  let result := 
    List.map 
      (fun x => interpret_trigger_contains_aux x tf) a
  in flatten_option_list result.

Ltac2 rec interpret_trigger (t : trigger) :=
  match t with
    | TIs a b => interpret_trigger_is a b
    | TContains a b => interpret_trigger_contains a b
    | TConj t1 t2 => 
      match interpret_trigger t1 with
        | Some res => 
          match interpret_trigger t2 with
            | Some res' => Some res' 
            | None => None
          end
        | None => None
      end              
    | TDisj t1 t2 => 
      match interpret_trigger t1 with 
        | Some res => Some res
        | None => 
          match interpret_trigger t2 with
            | Some res' => Some res'
            | None => None
          end
      end
  end.

(* The name of the tactic triggered + on which hypothesis it should be triggered *)
Ltac2 (* mutable *) triggered_tactics : (string*(constr_quoted list)) list := [].

Ltac2 trigger_tac_equal (x: string*(constr_quoted list)) (y: string*(constr_quoted list)) :=
  match x, y with
    | (s1, l1), (s2, l2) => Bool.and (String.equal s1 s2) (List.equal (fun x y =>
      let x' := constr_quoted_to_constr x in
      let y' := constr_quoted_to_constr y in 
      equal x' y') l1 l2)
  end. 

(** Triggers for tactics **)

Ltac2 trigger_and_intro := TIs TGoal (TAnd TDiscard TDiscard).
Ltac2 trigger_axiom := TIs TGoal (TVar TSomeHyp).
Ltac2 trigger_intro := TIs TGoal (TArr TDiscard TDiscard).
Ltac2 trigger_or_elim := TIs TSomeHyp (TOr TMetaVar TMetaVar).
Ltac2 trigger_left := TIs TGoal (TOr (TVar TSomeHyp) TDiscard).
Ltac2 trigger_right := TIs TGoal (TOr TDiscard (TVar TSomeHyp)).

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

Ltac2 Type Thunk := [ NoArg (unit-> unit) | WithArgs (constr list -> unit)].

Ltac2 thunksplit := fun () => apply_ltac1 ltac1val:(split) [].
Ltac2 thunkassumption := fun () => apply_ltac1 ltac1val:(assumption) [].
Ltac2 thunkintro := fun () => apply_ltac1 ltac1val:(intro) [].
Ltac2 thunkorelim (l : constr list) := apply_ltac1 ltac1val:(or_elim') l.
Ltac2 thunkleft := fun () => apply_ltac1 ltac1val:(left) [].
Ltac2 thunkright := fun () => apply_ltac1 ltac1val:(right) [].

Ltac2 trigs () :=
  [(NoArg thunksplit, trigger_and_intro, "split"); 
   (NoArg thunkintro, trigger_intro, "intro");
  (NoArg thunkassumption, trigger_axiom, "assumption");
  (WithArgs thunkorelim, trigger_or_elim, "or_elim");
  (NoArg thunkleft, trigger_left, "left");
  (NoArg thunkright, trigger_right, "right")].

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

Ltac2 run (thunk : Thunk) := 
  match thunk with
    | NoArg t => t ()
    | WithArgs _ => fail "does not run a thunk which takes arguments"
  end.

Ltac2 run_list (l: constr list) (thunk : Thunk) :=
  match thunk with
    | NoArg _ => fail "does not run a thunk with no arguments"
    | WithArgs t => t l
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
                  run tac
                else run_list (List.map (fun x => constr_quoted_to_constr x) l) tac ;
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
Set Default Proof Mode "Classic".

Goal (forall (A B C D : Prop), A -> B -> C -> D -> (A /\ B /\ C /\ D)).
orchestrator. Qed.

Goal (forall (A B : Prop), A \/ B -> B \/ A).
orchestrator. assumption. Qed.

End tests.












