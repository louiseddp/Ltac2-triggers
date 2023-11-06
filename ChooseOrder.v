Require Import List.
Import ListNotations.
Require Import Bool.
(* A small attempt to formalize the necessary conditions 
the orchestrator should meet, and to look for a suitable order *)

Notation "x .1" := (fst x) (at level 60).
Notation "x .2" := (snd x) (at level 60).

Definition foldi {A B: Type} (f: nat -> B -> A -> B) (l: list A) (acc: B) : B :=
  let fix aux f l n acc :=
  match l with
    | [] => acc
    | x :: xs => aux f xs (S n) (f n acc x)
  end
  in aux f l 0 acc.

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
Nat.eqb (length l1) (length l2).

Record CoqGoal := mkCoqGoal 
{ Hs : hyps ;
G : goal;
samelength : forallb (same_length G) Hs = true }. 

Definition transfo := (SimplifiedTriggers*Alterations)%type.

Record input := mkInput 
{ Transfos: list transfo ;
  CG: CoqGoal ;
  inv: length (G CG) = length Transfos }.

(* The hypothesis (or the goal) has been seen by
the nth-transformation *)

Fixpoint seen_n (n: nat) (l: list bool) :=
  match n with
    | 0 => 
      match l with
        | [] => []
        | x :: xs => true :: xs
      end
    | S n' => 
      match l with
        | [] => []
        | x :: xs => x :: seen_n n' xs
      end
  end.

Fixpoint seen_n_list (n: nat) (l: list (list bool)) :=
  match l with
    | [] => []
    | x :: xs => 
      if Bool.eqb (nth n x true) false 
      then seen_n n x :: xs
      else x :: seen_n_list n xs
    end.

(* Compute seen_n_list 2 [[true; true; true]; [true; false; true]; [true; false; false]]. *)
        
(* A new hypothesis has not been "seen" by 
any of the n transformations *) 

Fixpoint NewHyp (n: nat) :=
  match n with
    | 0 => []
    | S n => false :: NewHyp n
  end.

Definition ResetFalse (l: list bool) :=
  List.map (fun _ => false) l.

Definition SeenHyp (n: nat) (l: list bool) := Bool.eqb (nth n l false) true.

Definition SeenHyps (n: nat) (l: list (list bool)) :=
forallb (SeenHyp n) l.


(* Specification for the moment when the orchestrator
should stop: the transformations have all been 
applied and their trigger checked *)

Definition AllTrue (l: list bool) :=
forallb (Bool.eqb true) l.

Definition AllTrueList (l: list (list bool)) :=
forallb AllTrue l.

Definition EndOrchCoqGoal (cg: CoqGoal) :=
AllTrueList (Hs cg) && AllTrue (G cg).

Definition EndOrch (inp: input) : bool :=
EndOrchCoqGoal (CG inp).


(* Definition of the check_trigger function: 
the transformation n will check if it can be applied to
either one hypothesis (the first non-marked as "seen") 
if it is triggered by hyps, 
or the goal, and it will mark the corresponding hyp or goal 
as "seen" *)

Lemma seen_n_length (n: nat) (l: list bool) :
length (seen_n n l) = length l.
Proof.
generalize dependent l.
induction n as [| n IHn].
- destruct l ; reflexivity.
- simpl. destruct l.
  * reflexivity.
  * simpl in *. rewrite IHn. reflexivity. 
Qed.

Lemma seen_n_list_length (n: nat) (lb : list bool) (l: list (list bool)) :
forallb (same_length lb) l = true ->
forallb (same_length lb) (seen_n_list n l) = true.
Proof.
generalize dependent lb.
generalize dependent n.
induction l as [| x l IHl] ; intros n lb H.
- reflexivity.
- destruct (Bool.eqb (nth n x true) false) eqn:E.
  * simpl in *; rewrite E. destruct n.
     + destruct x ; simpl in *.
        { inversion E. }
        { rewrite eqb_true_iff in E. rewrite E in H.
apply andb_prop in H. destruct H as [H1 H2]. rewrite H2.
unfold same_length in *. simpl in *. rewrite H1. reflexivity. }
      + destruct x ; simpl in *.
        { inversion E. }
        { rewrite eqb_true_iff in E.
apply andb_prop in H. destruct H as [H1 H2].
rewrite H2. unfold same_length in *. simpl in *.
rewrite seen_n_length. rewrite H1. reflexivity. }
  * simpl in *. rewrite E.
apply andb_prop in H. destruct H as [H1 H2].
simpl in *. rewrite H1. simpl. apply IHl.
assumption. 
Qed.

Lemma seen_n_length_goal (n: nat) (cg: CoqGoal):
forallb (same_length (G cg)) (Hs cg) = true ->
forallb (same_length (seen_n n (G cg))) (Hs cg) = true.
Proof.
intro H.
unfold same_length in *.
rewrite seen_n_length. assumption. 
Qed. 

Lemma seen_n_length_hyp (n: nat) (cg: CoqGoal):
forallb (same_length (G cg)) (Hs cg) = true ->
forallb (same_length (G cg)) (seen_n_list n (Hs cg)) = true.
Proof.
intro H. rewrite seen_n_list_length.
- reflexivity.
- assumption.
Qed.

Definition check_trigger (tr: transfo) (n: nat) (cg: CoqGoal) :=
  match tr.1 with
    | GoalSensitive => 
      {| Hs := Hs cg;
         G := seen_n n (G cg);
         samelength := seen_n_length_goal n cg (samelength cg)
      |}
    | HypsSensitive => 
      {| Hs := seen_n_list n (Hs cg);
         G := G cg;
         samelength := seen_n_length_hyp n cg (samelength cg)
      |}
    | AllSensitive => 
      if SeenHyps n (Hs cg) then
      {| Hs := Hs cg;
         G := seen_n n (G cg);
         samelength := seen_n_length_goal n cg (samelength cg)
      |}
      else 
      {| Hs := seen_n_list n (Hs cg);
         G := G cg;
         samelength := seen_n_length_hyp n cg (samelength cg)
      |}
  end.

(* Definition of the apply function: 
the transformation applies its effect 
according to the constructor from the Alterations enumeration *)

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

Lemma resetfalse_length_forall2 l ls : 
forallb (same_length l) ls = true -> 
forallb (same_length (ResetFalse l)) ls = true.
Proof.
unfold same_length. rewrite resetfalse_length1. intro H.
assumption. 
Qed.

Lemma resetfalse_length_forall3 l ls : 
forallb (same_length l) ls = true ->
forallb (same_length (ResetFalse l)) (List.map ResetFalse ls) = true.
Proof.
intros H.
rewrite resetfalse_length_forall. reflexivity. 
rewrite resetfalse_length_forall2. reflexivity.
assumption.
Qed.

Definition apply (tr: transfo) (cg: CoqGoal) :=
  match tr.2 with
    | ProducesHyp => 
      {| Hs := NewHyp (length (G cg)) :: (Hs cg);
         G := G cg;
         samelength := new_hyp_length_goal cg
      |}
    | ChangesHyps => 
      {| Hs := List.map ResetFalse (Hs cg);
         G := G cg;
         samelength := resetfalse_length_forall (G cg) (Hs cg) (samelength cg)
      |}
    | ChangesGoal =>
      {| Hs := Hs cg;
         G := ResetFalse (G cg);
         samelength := resetfalse_length_forall2 (G cg) (Hs cg) (samelength cg)
      |}
    | ChangesAll =>
      {| Hs := List.map ResetFalse (Hs cg);
         G := ResetFalse (G cg);
         samelength := resetfalse_length_forall3 (G cg) (Hs cg) (samelength cg)
      |}
  end. 


(* Prepare an input: the transformations that applies 
only on the goal mark as "seen" all the hypotheses, 
the transformations that applies only on the hypotheses mark 
as "seen" the goal.
This should be done at the begining of the computation 
but also between each application of a transformation
All correct inputs should verify the Prepared predicate *)

Definition prepare_step (n: nat) (cg: CoqGoal) (tr: transfo) :=
  match tr.1 with
    | AllSensitive => cg
    | HypsSensitive => 
      {| Hs := Hs cg;
         G := seen_n n (G cg);
         samelength := seen_n_length_goal n cg (samelength cg)
      |}
    | GoalSensitive => 
      {| Hs := seen_n_list n (Hs cg);
         G := G cg;
         samelength := seen_n_length_hyp n cg (samelength cg)
      |}
  end. 

Axiom FF : forall A, A.

Definition prepare_steps (l: list transfo) (cg: CoqGoal) :=
foldi prepare_step l cg.

Definition prepare (inp: input) : input :=
{| Transfos := Transfos inp;
   CG := prepare_steps (Transfos inp) (CG inp) ;
   inv := FF (length
    (G
       (prepare_steps (Transfos inp)
          (CG inp))) =
  length (Transfos inp))
|}.



