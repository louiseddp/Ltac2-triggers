From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Init.
From Ltac2 Require Import Constr.
From Ltac2 Require Import Std.
From Ltac2 Require Import Env.
From Ltac2 Require Import Printf.
Import Unsafe.
Set Default Proof Mode "Classic".

Ltac2 Type flag_arg :=
  [ Flag_type | Flag_term | Flag_unneeded ].

Ltac2 Type trigger_var := 
  [TGoal | TSomeHyp].

(* TODO ask the diff between meta and evar in Constr.v file *)

Ltac2 Type trigger_sort :=
[ TProp | TSet | TBigType].

(* warning: does not mention free variables, 
and does not handle universes, native arrays, integers, 
projections or floats *)
Ltac2 Type rec trigger_term := [

(* follows the constr type *)
| TVar (string option, flag_arg) (* local variable or section variable *)
| TSort (trigger_sort) (* simplification of universes *)
| TProd (trigger_term, trigger_term)
| TLambda (trigger_term, trigger_term)
| TLetIn (trigger_term, trigger_term, trigger_term)
| TApp (trigger_term, trigger_term)
| TConstant (string option, flag_arg)
| TInd (string option, flag_arg)
| TConstructor (string option, flag_arg)
| TCase (trigger_term, trigger_term, trigger_term list option) 
| TFix (trigger_term, trigger_term)
| TCoFix (trigger_term, trigger_term)

(* specific to triggers *)
| TType (constr, bool)
| TTerm (constr, bool)
| TTrigVar (trigger_var, flag_arg)
| TAny (flag_arg) 

(* less fine-grained structure *)
| TEq (trigger_term, trigger_term, trigger_term)
| TAnd (trigger_term, trigger_term)
| TOr (trigger_term, trigger_term)
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

(* warning: does not take let ins into account 
warning 2: returns only the first suitable hypothesis *)
Ltac2 interpret_trigger_var_with_constr cg tv c :=
  let itv := interpret_trigger_var cg tv in
    match itv with
      | Hyps hyps => 
          let l := List.find_all (fun (_, _, z) => equal z c) hyps in 
            match l with
              | [] => None
              | (_, _, z) :: xs => Some z
            end
      | Goal (Some g) => if equal g c then Some g else None
      | Goal None => None
    end.

Ltac2 destruct_eq (c : constr) :=
  match kind c with
    | App c' ca => 
        if equal c' '(@eq) then 
          let ty := Array.get ca 0 in
          let c1 := Array.get ca 1 in
          let c2 := Array.get ca 2 in
          Some (ty, c1, c2)
        else None
    | _ => None
  end. 

Ltac2 destruct_and (c : constr) :=
  match kind c with
    | App c' ca => 
        if equal c' 'and then 
          let c1 := Array.get ca 0 in
          let c2 := Array.get ca 1 in
          Some (c1, c2)
        else None
    | _ => None
  end.

Ltac2 destruct_or (c : constr) :=
  match kind c with
    | App c' ca => 
        if equal c' 'or then 
          let c1 := Array.get ca 0 in
          let c2 := Array.get ca 1 in
          Some (c1, c2)
        else None
    | _ => None
  end.

(* In this new version, the comparison between constrs and triggers may not be
sufficiently accurate because 
free variables should be matched against TAnys, and some triggers cannot have arguments *)


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

Ltac2 rec interpret_trigger_term_with_constr
 cg (c : constr) (tte : trigger_term) : constr list option:=
  match kind c, tte with
    | App _ _, TEq tte1 tte2 tte3 => 
        match destruct_eq c with
          | Some (c1, c2, c3) => 
              match interpret_trigger_term_with_constr cg c1 tte1 with
                | Some l => 
                    match interpret_trigger_term_with_constr cg c2 tte2 with
                      | Some l' => 
                          match interpret_trigger_term_with_constr cg c3 tte3 with
                            | Some l'' => Some (List.append (List.append l l') l'')
                            | None => None
                          end
                      | None => None
                    end
                | None => None
              end
          | None => None
        end
    | App _ _, TAnd tte1 tte2 => 
        match destruct_and c with
          | Some (c1, c2) =>
              match interpret_trigger_term_with_constr cg c1 tte1 with
                | Some l => 
                    match interpret_trigger_term_with_constr cg c2 tte2 with
                      | Some l' => Some (List.append l l')
                      | None => None
                    end
                | None => None
              end
          | None => None
        end
    | App _ _, TOr tte1 tte2 => 
        match destruct_or c with
          | Some (c1, c2) =>
              match interpret_trigger_term_with_constr cg c1 tte1 with
                | Some l => 
                    match interpret_trigger_term_with_constr cg c2 tte2 with
                      | Some l' => Some (List.append l l')
                      | None => None
                    end
                | None => None
              end
          | None => None
        end
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
        let res := interpret_trigger_term_with_constr cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg t tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
    | Lambda bi t, TLambda tte1 tte2 => 
        let ty := Binder.type bi in
        let res := interpret_trigger_term_with_constr cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg t tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
    | LetIn bi t t', TLetIn tte1 tte2 tte3 => 
        let ty := Binder.type bi in
        let res := interpret_trigger_term_with_constr cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg t tte2 in
                  match res' with
                    | Some l' => 
                        let res'' := interpret_trigger_term_with_constr cg t' tte3 in
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
        let res := interpret_trigger_term_with_constr cg c tte1 in
          match res with
            | Some l => 
                let c' := Array.get ca 0 in
                let res' := interpret_trigger_term_with_constr cg c' tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
       else 
        let c' := curry_app c ca in interpret_trigger_term_with_constr cg c' tte
(* Constant, inductives, constructors : 
only equalities up to universes in order to simplify 
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
    | Case _ ty _ t ca, TCase tte1 tte2 o =>
       let res := interpret_trigger_term_with_constr cg ty tte1 in
        match res with
          | Some l => 
              let res' := interpret_trigger_term_with_constr cg ty tte2 in
                match res' with
                  | Some l' =>
                      match o with
                        | Some lc =>
                            let branchs := Array.to_list ca in
                            let rec aux branchs lc acc :=
                              match branchs, lc with
                                | [], [] => Some acc
                                | x :: xs, y :: ys => 
                                    let res'' := interpret_trigger_term_with_constr cg x y in
                                      match res'' with
                                        | Some l'' => aux xs ys (List.append l'' acc)
                                        | None => None
                                      end
                                | _, _ => None
                              end 
                            in 
                              match aux branchs lc [] with
                                | Some l'' => Some (List.append (List.append l l') l'')
                                | None => None
                              end
                        | None => Some (List.append l l')
                      end
                  | None => None
                end
          | None => None
        end
    | Fix _ nbmut binds ca, TFix tte1 tte2 => 
        let ty := Binder.type (Array.get binds nbmut) in
        let res := interpret_trigger_term_with_constr cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg (Array.get ca nbmut) tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
    | CoFix nbmut binds ca, TCoFix tte1 tte2 =>
        let ty := Binder.type (Array.get binds nbmut) in
        let res := interpret_trigger_term_with_constr cg ty tte1 in
          match res with
            | Some l => 
                let res' := interpret_trigger_term_with_constr cg (Array.get ca nbmut) tte2 in
                  match res' with
                    | Some l' => Some (List.append l l')
                    | None => None
                  end
            | None => None
          end
    | _, TTerm c' b => 
      if equal c c' then 
        if b then Some [c']
        else Some [] 
      else None
    | _, TType t b => 
        if equal (Constr.type c) t then
          if b then Some [t]
          else Some []  
        else None
    | _, TTrigVar v fl => 
      let opt := interpret_trigger_var_with_constr cg v c in
        match opt with
          | Some t => 
              match fl with
                | Flag_term => Some [t]
                | Flag_type => Some [type t]
                | Flag_unneeded => Some []
              end
          | None => None
        end
    | _, TAny fl => 
      match fl with
        | Flag_term => Some [c]
        | Flag_type => Some [type c]
        | Flag_unneeded => Some []
      end
    | _, _ => None
  end.




