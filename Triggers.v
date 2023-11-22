From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Init.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Std.
From Ltac2 Require Import Env.
Import Unsafe.
Set Default Proof Mode "Classic".

Ltac2 Type flag_arg :=
  [ Flag_type | Flag_term | Flag_unneeded ].

Ltac2 Type trigger_var := 
  [TGoal | TSomeHyp].

(* TODO ask the diff between meta and evar in Constr.v file *)

Ltac2 Type trigger_sort :=
[ TProp | TSet | TBigType].

(* does not mentions free variables, 
and does not handle universes, native arrays, integers, 
projections or floats *)
Ltac2 Type rec trigger_term := [
| TVar (string option, flag_arg) (* local variable or section variable *)
| TSort (trigger_sort) (* simplification of universes *)
| TProd (trigger_term, trigger_term)
| TLambda (trigger_term, trigger_term)
| TLetIn (trigger_term, trigger_term, trigger_term)
| TApp (trigger_term, trigger_term)
| TConstant (string option, flag_arg)
| TInd (string option, flag_arg)
| TConstructor (string option, flag_arg)
| TCase (trigger_term list)
| TFix (trigger_term, trigger_term)
| TCoFix (trigger_term, trigger_term)
| TEq (trigger_term, trigger_term, trigger_term)
| TType (constr, bool)
| TTerm (constr, bool)
| TTrigVar (trigger_var, flag_arg)
| TArr (trigger_term, trigger_term)
| TAnd (trigger_term, trigger_term)
| TOr (trigger_term, trigger_term)
| TAny (flag_arg) 
].

Ltac2 tArg := TAny Flag_term.
Ltac2 tArgType := TAny Flag_type.
Ltac2 tDiscard := TAny Flag_unneeded.

Ltac2 rec tApp_nary (tc : trigger_term) (ltc : trigger_term list) := 
  match ltc with
    | [] => tc
    | x :: xs => tApp_nary (TApp tc x) xs
  end.

Ltac2 Type rec trigger := [
  | TIs (trigger_var, trigger_term) 
  | TPred (trigger_var, constr -> bool) (* the trigger_var should verify the user-defined Ltac2 predicate *)
  | TContains (trigger_var, trigger_term)
  | TConj (trigger, trigger) (* two triggers need to be present at the same time *)
  | TDisj (trigger, trigger) (* one of the two triggers needs to be present *)
  | TNot (trigger) (* negation of a trigger *)
  ].

Ltac2 Type hyps_or_goal := [
  | Hyps ((ident*constr option*constr) list) 
  | Goal (constr option)].

Ltac2 interpret_trigger_var cg (tv: trigger_var) :=
  let (hyps, g) := cg in
    match tv with
      | TSomeHyp => Hyps hyps
      | TGoal => Goal g
    end.

(* In this new version, the comparison between constrs and triggers may not be
sufficiently accurate because 
free variables produces TODO, and some triggers cannot have arguments *)


(* Ltac2 Type kind := [
| Case (case, constr, case_invert, constr, constr array)
| Fix (int array, int, binder array, constr array)
| CoFix (int, binder array, constr array)
]. *)

Ltac2 curry_app (c : constr) (ca : constr array) :=
  let cl := Array.to_list ca in
  let rec tac_rec c cl := 
    match cl with
      | [] => c
      | x :: xs => tac_rec (make (App c (Array.of_list [x]))) xs
    end
  in tac_rec c cl. 

Ltac2 ref_equal_upto_univs (r1 : reference) (r2 : reference) :=
  match r1, r2 with
    | VarRef id1, VarRef id2 => Ident.equal id1 id2
    | ConstRef c1, ConstRef c2 => 
        let t1 := instantiate r1 in
        let t2 := instantiate r2 in 
        equal t1 t2
    | IndRef _, IndRef _ =>
        let t1 := instantiate r1 in
        let t2 := instantiate r2 in 
        equal t1 t2
    | ConstructRef _, ConstructRef _ => 
        let t1 := instantiate r1 in
        let t2 := instantiate r2 in 
        equal t1 t2
    | _ => false
  end.

Ltac2 matching_ref (o : string option) (r : reference) :=
  match o with
    | Some s =>
        let o' := Ident.of_string s in
          match o' with
            | None => false
            | Some id =>
                let refs := expand [id] in
                List.exist (ref_equal_upto_univs r) refs
          end
    | None => true
  end.

Ltac2 rec interpret_constr_with_trigger_term
 cg (c : constr) (tte : trigger_term) : constr list option:=
  match kind c, tte with
(* De Brujin indexes: cannot be given as arguments to the tactic triggered. Otherwise 
the variable would escape its scope. We can only use their type, or discard them. *)
    | Rel _, TType c' b => 
        let ty := type c in
        if equal c c' then
          if b then Some [c]
        else Some []
        else None
    | Rel _, TAny Flag_type => Some [type c]
    | Rel _, TAny Flag_unneeded => Some []
    | Rel _, TAny Flag_term => None (* We prevent using a Rel k as argument *)
(* Local (or section) variables *)
    | Var id, TVar o fl => 
        match o with
          | Some s =>
              match Ident.of_string s with
                | Some id' =>
                    if Ident.equal id id' then
                      match fl with
                        | Flag_term => Some [c]
                        | Flag_type => Some [type c]
                        | Flag_unneeded => Some []
                      end
                    else None
                | None => None
              end
          | None => 
              match fl with
                | Flag_term => Some [c]
                | Flag_type => Some [type c]
                | Flag_unneeded => Some []
              end
          end
(* Sorts: we do not want to deal with universes, as we are afraid 
this may introduce difficulties which are unrelated to our main goal, 
but we want to distinguish between Prop, Set and Type_i, i > 1 *)
    | Sort s, TSort ts =>
        match ts with
          | TProp => if equal c 'Prop then Some [] else None
          | TSet => if equal c 'Set then Some [] else None
          | TBigType => 
            if Bool.and (equal c 'Type) (Bool.neg (equal c 'Set))
            then Some [] else None
        end
    | Prod bi t, TProd tte1 tte2 => 
        let ty := Binder.type bi in
        let res := interpret_constr_with_trigger_term cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_constr_with_trigger_term cg t tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
    | Lambda bi t, TLambda tte1 tte2 => 
        let ty := Binder.type bi in
        let res := interpret_constr_with_trigger_term cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_constr_with_trigger_term cg t tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
    | LetIn bi t t', TLetIn tte1 tte2 tte3 => 
        let ty := Binder.type bi in
        let res := interpret_constr_with_trigger_term cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_constr_with_trigger_term cg t tte2 in
                  match res' with
                    | Some l' => 
                        let res'' := interpret_constr_with_trigger_term cg t' tte3 in
                          match res'' with
                            | Some l'' => Some (List.append (List.append l l') l'')
                            | None => None
                          end
                    | None => None
                  end
            | None => None
          end
(* Application case : Some adjustments are made to be sure 
that we have binary apps on both sides *)  
    | App c ca, TApp tte1 tte2 => 
       if Int.le (Array.length ca) 1 then
        let res := interpret_constr_with_trigger_term cg c tte1 in
          match res with
            | Some l => 
                let c' := Array.get ca 0 in
                let res' := interpret_constr_with_trigger_term cg c' tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
       else 
        let c' := curry_app c ca in interpret_constr_with_trigger_term cg c' tte
(* Constant, inductives, constructors : only monomorphic universes in order to simplify 
the interpretation of our triggers *)
    | Constant cst _, TConstant o fl =>
        if matching_ref o (ConstRef cst) then 
          match fl with
            | Flag_term => Some [c]
            | Flag_type => Some [type c]
            | Flag_unneeded => Some []
          end
        else None
    | Ind ind _, TInd o fl =>
        if matching_ref o (IndRef ind) then 
          match fl with
            | Flag_term => Some [c]
            | Flag_type => Some [type c]
            | Flag_unneeded => Some []
          end
        else None
    | Constructor cstr _, TConstructor o fl =>
        if matching_ref o (ConstructRef cstr) then 
          match fl with
            | Flag_term => Some [c]
            | Flag_type => Some [type c]
            | Flag_unneeded => Some []
          end
        else None
    | _, _ => None
  end.




