From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Require Import Utils.
Set Default Proof Mode "Classic".

(** Triggers **)

Ltac2 Type flag_arg :=
  [ FType | FTerm | FNothing].

Ltac2 Type trigger_var := 
  [TGoal | TSomeHyp].

Ltac2 Type rec trigger_form := [
  | TType (constr, bool)
  | TTerm (constr, bool)
  | TVar (trigger_var, flag_arg)
  | TArr (trigger_form, trigger_form)
  | TAnd (trigger_form, trigger_form)
  | TOr (trigger_form, trigger_form)
  | TAny (bool) ].

Ltac2 tMetavar := TAny true.
Ltac2 tDiscard := TAny false.

(* Notation "<% x %>" := ltac2:(let x := Ltac2.Constr.pretype x in TTerm x false).  *)

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
        (type_of_hyps h)
    | TGoal => let g := Control.goal () in [g]
  end.

Ltac2 rec interpret_constr_with_trigger_form 
  (c : constr_quoted) (tf : trigger_form) :=
  match c, tf with
    | Term c, TTerm c' b => 
      if equal c c' then 
        if b then Some [c']
        else Some [] 
      else None
    | Term c, TType t b => 
        if equal (Constr.type c) t then
          if b then Some [t]
          else Some []  
        else None 
    | Term c, TVar v fl => 
       let tv := interpret_trigger_var v in
       if List.mem equal c tv then 
         match fl with
          | FNothing => Some []
          | FType => Some tv
          | FTerm => Some [get_hyp c]
         end
       else None
    | _, TAny b => if b then Some [constr_quoted_to_constr c] else Some []
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