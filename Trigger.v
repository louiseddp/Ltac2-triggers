From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.

(** Utilities **)

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

(** Interpretation **)

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

Ltac2 rec interpret_constr_with_trigger_form 
  (c : constr_quoted) (tf : trigger_form) :=
  match c, tf with
    | Top, TTop => Some [] 
    | Bottom, TBottom => Some []
    | Term c, TTerm c' => if equal c c' then Some [] else None
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

Ltac2 interpret_trigger (t : trigger) :=
  match t with
    | TEq a b => interpret_trigger_eq a b
    | TIs a b => interpret_trigger_is a b
    | TContains a b => interpret_trigger_contains a b
  end.

Ltac2 mutable triggered_tactics := [].

Ltac2 trigger_and_intro := TIs TGoal (TAnd TDiscard TDiscard).

Ltac2 trigger_axiom := TEq TGoal TSomeHyp.

Ltac2 thunksplit := fun () => ltac1:(split).

Ltac2 thunkassumption := fun () => ltac1:(assumption).

Ltac2 trigs () :=
  [(thunksplit, trigger_and_intro, "split"); 
  (thunkassumption, trigger_axiom, "assumption")].

Ltac2 run (thunk : unit -> unit) := thunk ().

Ltac2 orchestrator () :=
  let rec trigger' t :=
    match t with
    | [] => Message.print (Message.of_string "no trigger found")
    | (tac, trig, message) :: triggers' =>
        match interpret_trigger trig with
          | Some l =>
            if Bool.neg (Int.equal (List.length l) 0) (* List.mem equal triggered_tactics l  TODO *) then
              Message.print (Message.of_string "Trigger already applied\n");
              trigger' triggers'
            else
              Message.print (Message.concat 
                (Message.of_string "Automaticaly applied ") (Message.of_string message));
(* TODO update reference of triggered *)
              run tac
          | None => trigger' triggers'
        end
    end
  in
  trigger' (trigs ()).


Goal (forall (A B C D : Prop), A -> B -> C -> D -> (A/\B/\C/\D)).
intros. orchestrator (). Qed.













