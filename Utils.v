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

(** and_elim **) 

Ltac and_elim A B :=
match goal with
| H : A /\ B |- _ => 
let H1 := fresh in assert (H1 : A) by apply H ;
let H2 := fresh in assert (H2 : B) by apply H
| _ => idtac
end.

Goal forall (A B : Prop), A /\ B -> False.
Proof.
intros A B H. and_elim A B. Abort.

(** Utilities **)

Ltac2 third_arg_equal (x : 'a*'b*'c) (y : 'a*'b*'c) (eq : 'c -> 'c -> bool) :=
  match x, y with
    | (_, _, u1), (_, _, u2) => eq u1 u2
  end.


Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 rec type_of_hyps (l : (ident * constr option * constr) list) :=
  match l with
    | [] => []
    | (id, opt, ty) :: xs => ty :: type_of_hyps xs
  end.

Ltac2 get_hyp (c : constr) :=
  let h := Control.hyps () in
  let rec tac_aux c h := 
  match h with
    | [] => fail "not found"
    | (id, opt, ty) :: xs => 
        let h' := Control.hyp id in 
        if Constr.equal c (Constr.type h') then h' 
        else tac_aux c xs
  end in tac_aux c h.

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
