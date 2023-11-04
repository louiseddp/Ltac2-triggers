Require Import List.
Import ListNotations.
Require Import Bool.
(* A small attempt to formalize the necessary conditions 
the orchestrator should meet, and to look for a suitable order *)

Notation "x .1" := (fst x) (at level 60).
Notation "x .2" := (snd x) (at level 60).


Inductive SimplifiedTriggers : Set :=
GoalSensitive | HypsSensitive | AllSensitive.

Inductive Alterations : Set :=
ProducesHyp | ChangesHyps | ChangesGoal | ChangesAll.

Definition hyp := list bool.

Definition hyps := list (list bool).

Definition goal := list bool.

Fixpoint eqb (l1 l2: list bool) :=
  match l1, l2 with
    | [], [] => true
    | [], _ :: _ => false
    | _ :: _, [] => false
    | x :: xs, y :: ys => Bool.eqb x y && eqb xs ys
  end. 

Fixpoint Inb (h: list bool) (hs: list (list bool)) : bool :=
  match hs with
    | [] => false
    | h' :: hs => eqb h h' || Inb h hs
  end.

Definition same_length {A : Type} (l1 l2: list A) :=
Nat.eqb (length l1) (length l2). Print forallb.

Record CoqGoal := mkCoqGoal 
{ Hs : hyps ;
G : goal;
samelength : forallb (same_length G) Hs = true }. 

Definition transfo := (SimplifiedTriggers*Alterations)%type.

(* A new hypothesis has not been "seen" by 
any of the n transformations *) 

Fixpoint NewHyp (n: nat) :=
  match n with
    | 0 => []
    | S n => false :: NewHyp n
  end.

Definition ResetFalse (l: list bool) :=
  List.map (fun _ => false) l.

Lemma new_hyp_length_goal_aux (l : list bool) :
  same_length l (NewHyp (length l)) = true.
Proof.
induction l as [ | x l' IHl'].
- reflexivity.
- unfold same_length in *. assumption. 
Qed.

Lemma new_hyp_length_goal (cg: CoqGoal) :
  forallb (same_length (G cg)) ((NewHyp (length (G cg))) :: (Hs cg)) = true.
Proof.
destruct cg as [hs g same_length].
simpl in *. rewrite new_hyp_length_goal_aux.
rewrite same_length. reflexivity. 
Qed.

Lemma resetfalse_length1 (l: list bool) :
length l = length (ResetFalse l).
Proof.
induction l as [ | x l IHl].
- reflexivity.
- simpl. rewrite IHl. reflexivity. 
Qed. 

Lemma resetfalse_length (l l' : list bool) :
same_length l l' = true ->
same_length l (ResetFalse l') = true.
Proof.
induction l' as [ | x l' IHl'].
- destruct l; [reflexivity | ..]. intro H. unfold same_length in H. inversion H.
- destruct l; unfold same_length in *; simpl in *;
[ intro H; inversion H | ..]. rewrite <- resetfalse_length1.
trivial. Qed.

Lemma resetfalse_length_forall l ls : 
forallb (same_length l) ls = true -> 
forallb (same_length l) (List.map ResetFalse ls) = true.
Proof.
induction ls as [ | x ls' IHls'].
- reflexivity.
- simpl. intro H. apply andb_prop in H. destruct H as [H1 H2]. 
rewrite resetfalse_length.
apply IHls' in H2. rewrite H2. reflexivity. assumption.
Qed.

Definition apply (tr: transfo) (cg: CoqGoal) :=
  match tr.2 with
    | ProducesHyp => 
      {| Hs := NewHyp (length (G cg)) :: (Hs cg);
         G := G cg;
         samelength := new_hyp_length_goal cg
      |}
    | ChangesHyps => 
      let (hs, g) := cg in
      (List.map ResetFalse hs, g)
    | ChangesGoal =>
      let (hs, g) := cg in
      (hs, ResetFalse g)
    | ChangesAll =>
      let (hs, g) := cg in
      (List.map ResetFalse hs, ResetFalse g)
  end.
