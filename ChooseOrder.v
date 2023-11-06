Require Import List.
Import ListNotations.
Require Import Bool.
(* A small attempt to formalize the necessary conditions 
the orchestrator should meet, and to look for a suitable order *)

Notation "x .1" := (fst x) (at level 60).
Notation "x .2" := (snd x) (at level 60).

Fixpoint foldi_aux {A B: Type} (f: nat -> B -> A -> B) (l: list A) (n: nat) (acc: B) : B :=
  match l with
    | [] => acc
    | x :: xs => f n (foldi_aux f xs (S n) acc) x
  end.

Definition foldi {A B} f l acc := @foldi_aux A B f l 0 acc.

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
Qed. Print SeenHyp.

Definition check_trigger 
(tr: transfo) 
(n: nat) 
(cg: CoqGoal) : option CoqGoal :=
  match tr.1 with
    | GoalSensitive => if SeenHyp n (G cg) then None else Some
      ({| Hs := Hs cg;
         G := seen_n n (G cg);
         samelength := seen_n_length_goal n cg (samelength cg)
      |})
    | HypsSensitive => if SeenHyps n (Hs cg) then None else Some
      ({| Hs := seen_n_list n (Hs cg);
         G := G cg;
         samelength := seen_n_length_hyp n cg (samelength cg)
      |})
    | AllSensitive => 
      if SeenHyps n (Hs cg) then 
      if SeenHyp n (G cg) then None else Some
      ({| Hs := Hs cg;
         G := seen_n n (G cg);
         samelength := seen_n_length_goal n cg (samelength cg)
      |})
      else Some
      ({| Hs := seen_n_list n (Hs cg);
         G := G cg;
         samelength := seen_n_length_hyp n cg (samelength cg)
      |})
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

Definition prepare_steps (l: list transfo) (cg: CoqGoal) :=
foldi prepare_step l cg.

Lemma prepare_step_length n cg tr :
length (G (prepare_step n cg tr)) = length (G cg).
Proof.
destruct cg as [hyps goal inv].
destruct goal as [ | x xs] ; 
destruct tr as (s, a); destruct s; destruct n.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- simpl in *. rewrite seen_n_length. reflexivity.
- simpl in *. reflexivity.  
- reflexivity. 
Qed.

Lemma prepare_steps_length n cg trs :
length
  (G (foldi_aux prepare_step trs n cg)) =
length (G cg).
Proof.
generalize dependent n.
generalize dependent cg.
induction trs as [| tr' trs IHtrs].
- reflexivity.
- simpl in *. intros cg n. specialize (IHtrs cg (S n)).
rewrite prepare_step_length. assumption.
Qed.
  

Lemma prepare_steps_length2 cg trs:
length (G (prepare_steps trs cg))
= length (G cg).
Proof.
unfold prepare_steps in *. 
unfold foldi. apply prepare_steps_length.
Qed. 

Lemma prepare_steps_length3 inp :
length (G (prepare_steps (Transfos inp) (CG inp))) = length (Transfos inp).
Proof.
destruct inp as [trs cg inv].
simpl. rewrite <- inv. apply prepare_steps_length2.
Qed.

Definition prepare (inp: input) : input :=
{| Transfos := Transfos inp;
   CG := prepare_steps (Transfos inp) (CG inp) ;
   inv := prepare_steps_length3 inp
|}.

Lemma prepare_length inp : 
length (Transfos (prepare inp)) = length (Transfos inp).
Proof. reflexivity. Qed.

(* One step: the input is "prepared" and 
then we applied the first transformation triggered *)

Axiom FF: forall A, A.

Fixpoint first_transfo_applied_aux 
(trs: list transfo) 
(cg: CoqGoal) 
(n: nat) : option (transfo*CoqGoal) :=
  match trs with
    | [] => None
    | tr :: trs' => 
      match check_trigger tr n cg with
        | None => first_transfo_applied_aux  trs' cg (S n)
        | Some cg' => Some (tr, cg')
      end
  end.

Definition first_transfo_applied trs cg :=
first_transfo_applied_aux trs cg 0.

Lemma first_transfo_applied_check_trigger trs cg n :
  match first_transfo_applied_aux trs cg n with
    | None => True
    | Some (tr, cg') =>
        match check_trigger tr n cg with 
          | None => True
          | Some cg'' => cg' = cg''
        end
  end.
Proof.
generalize dependent n.
generalize dependent cg.
induction trs as [ | tr trs IHtrs] ; intros cg n.
- simpl in *. exact I.
- destruct (first_transfo_applied_aux (tr :: trs) cg n) as [(tr1, cg1) | ] eqn:E.
  * destruct (check_trigger tr1 n cg) as [ cg2 | ] eqn:E1.
    simpl in E.


 destruct p as (tr1, cg1). 
    destruct (check_trigger tr1 n cg) eqn:E. 
    pose proof (IH' := IHtrs).
    specialize (IHtrs cg1). specialize (IHtrs n).
    destruct (first_transfo_applied_aux trs cg1 n) eqn:E1.
    destruct (check_trigger tr n cg1) eqn:E2.
    destruct p as (tr2, cg2).
    destruct (check_trigger tr2 n cg1) eqn:E3.
    subst.

 rewrite E2 in IHtrs.
 


destruct (first_transfo_applied_aux trs cg) eqn:E.
    * destruct p as (tr1, cg1). simpl.
destruct (check_trigger tr1 n cg) eqn:E'.
subst. destruct (check_trigger tr n cg) eqn:F.
rewrite F. reflexivity. 
destruct (first_transfo_applied_aux trs cg (S n)) eqn:F'.
destruct p as (tr2, cg2). destruct (check_trigger tr2 n cg) eqn:G.
s
 



  * simpl in *. destruct (check_trigger tr n cg) eqn:F.
rewrite F. reflexivity. 
destruct (first_transfo_applied_aux trs' cg (S n)) eqn:F'.
destruct p as (tr0, cg0). destruct (check_trigger tr0 n cg) eqn:G.
subst.
  * destruct (first_transfo_applied_aux (tr :: trs') cg) eqn:E''.
      { destruct p as (tr'', cg''). rewrite E'.
subst.
assert (H : tr'' = tr \/ tr'' = tr').
destruct (check_trigger tr 0 cg) eqn:F'.
unfold first_transfo_applied in E''.
rewrite F' in E''. inversion E''. left. reflexivity. 
unfold first_transfo_applied in E''. rewrite F' in E''.

destruct trs'. inversion E''. right.


    * destruct (first_transfo_applied (tr::trs') cg) eqn:E'.
unfold first_transfo_applied in E'.
destruct (check_trigger tr 0 cg) eqn:E''.
      + inversion E'. subst. exists 0. rewrite E''. reflexivity.
      + destruct trs'. inversion E'.

eexists.
destruct cg as [hyps g eq].
destruct tr as (s, a).
- destruct (check_trigger (s, a)) eqn:E'.
    * 

eexists.


Lemma first_transfo_applied_length_goal trs cg :
  match first_transfo_applied trs cg with
    | None => True
    | Some (_, cg') => length (G cg') = length (G cg)
  end.
Proof.
destruct (first_transfo_applied trs cg) as [ (tr, cg') | ] eqn:E.
- inversion E.



Lemma onestep_length inp :
  let inp' := prepare inp in
  match first_transfo_applied (Transfos inp') (CG inp') with
    | None => True
    | Some (tr, cg') => 
      let cg'' := apply tr cg' in
        length (G cg'') = length (Transfos inp)
   end.
Proof.
simpl.
destruct 
(first_transfo_applied (Transfos inp) (prepare_steps (Transfos inp) (CG inp))) 
as [ (tr, cg') |] eqn:E.
- destruct inp as [trs cg inv]; simpl. rewrite <- inv.

- exact I.




 "length (G cg'') = length (Transfos inp)"

Definition onestep (inp: input) : option input :=
  let inp' := prepare inp in
    match first_transfo_applied (Transfos inp') (CG inp') with
      | None => None
      | Some (tr, cg') =>
        let cg'' := apply tr cg' in Some
          ({| Transfos := Transfos inp;
             CG := cg'' ;
             inv := FF _
          |})
      end.






