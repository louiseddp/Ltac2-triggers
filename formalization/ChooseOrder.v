Require Import List.
Require Import Lia.
Import ListNotations.
Require Import Bool.
Require Import PeanoNat.
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

Scheme Equality for SimplifiedTriggers.

Inductive Alterations : Set :=
  ProducesHyp | ChangesHyps | ChangesGoal | ChangesAll.

Scheme Equality for Alterations.

Definition hyp := list bool.

Definition hyps := list (list bool).

Definition goal := list bool.

Definition same_length {A : Type} (l1 l2: list A) :=
Nat.eqb (length l1) (length l2).

Record CoqGoal := mkCoqGoal 
{ Hs : hyps ;
G : goal;
samelength : forallb (same_length G) Hs = true }. 

Definition transfo := (SimplifiedTriggers*Alterations)%type.

Definition transfo_eqb (tr tr': transfo) : bool := 
  match tr, tr' with
    | (st1, alt1), (st2, alt2) => 
      SimplifiedTriggers_beq st1 st2 && Alterations_beq alt1 alt2
  end.

Fixpoint find_aux (trs: list transfo) (tr: transfo) (n: nat) :=
  match trs with
    | [] => n
    | x :: xs => if transfo_eqb x tr then n else find_aux xs tr (S n)
  end.

Definition find trs tr := find_aux trs tr 0.

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

Lemma check_trigger_length tr n cg cg' :
check_trigger tr n cg = Some cg' -> length (G cg) = length (G cg').
Proof.
intro H. 
destruct tr as (s, a); destruct s ; unfold check_trigger in *;
simpl in *.
- destruct (SeenHyp n (G cg)) eqn:E.
  * inversion H.
  * inversion H; simpl. symmetry. apply seen_n_length.
- destruct (SeenHyps n (Hs cg)) eqn:E.
  * inversion H.
  * inversion H; reflexivity.
- destruct (SeenHyps n (Hs cg)) eqn:E; destruct (SeenHyp n (G cg)) eqn:E'.
  * inversion H.
  * inversion H; simpl. symmetry. apply seen_n_length.
  * inversion H; reflexivity.
  * inversion H; reflexivity.
Qed.

(* Definition of the apply function: 
the nth-transformation applies its effect 
according to the constructor from the Alterations enumeration 
*)

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

Lemma apply_length cg tr :
length (G cg) = length (G (apply tr cg)).
Proof.
destruct cg as [hyps g].
destruct tr as (a, s).
destruct s.
  - reflexivity.
  - reflexivity.
  - apply resetfalse_length1.
  - apply resetfalse_length1.
Qed. 


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

Fixpoint first_transfo_applied_aux 
(trs: list transfo) 
(cg: CoqGoal) 
(n: nat) : option (transfo*CoqGoal) :=
  match trs with
    | [] => None
    | tr :: trs' => 
      match check_trigger tr n cg with
        | None => first_transfo_applied_aux trs' cg (S n)
        | Some cg' => Some (tr, cg')
      end
  end.

Definition first_transfo_applied trs cg :=
first_transfo_applied_aux trs cg 0.

Lemma first_transfo_applied_length_goal trs cg n :
  match first_transfo_applied_aux trs cg n with
    | None => True
    | Some (_, cg') => length (G cg') = length (G cg)
  end.
Proof.
generalize dependent cg.
generalize dependent n.
induction trs as [ | tr trs IHtrs']; intros n cg.
- exact I.
- simpl. destruct (check_trigger tr n cg) as [cg' | ] eqn:E.
  * apply check_trigger_length in E. symmetry. assumption.
  * apply IHtrs'.
Qed.

Lemma onestep_length inp :
  let inp' := prepare inp in
  match first_transfo_applied (Transfos inp') (CG inp') with
    | None => True
    | Some (tr, cg') => 
      let cg'' := apply tr cg' in
        length (G cg'') = length (Transfos inp)
   end.
Proof.
unfold first_transfo_applied. simpl.
destruct (first_transfo_applied_aux (Transfos inp) 
(prepare_steps (Transfos inp) (CG inp)) 0) as [ (tr, cg) | ] eqn:E.
rewrite <- apply_length. pose proof (H := first_transfo_applied_length_goal).
specialize (H (Transfos inp) 
(prepare_steps (Transfos inp) (CG inp)) 0). rewrite E in H. 
rewrite prepare_steps_length3 in H. assumption.
exact I.
Qed. 

Lemma onestep_length2 inp inp' tr cg cg' :
inp' = prepare inp -> 
first_transfo_applied (Transfos inp') (CG inp') = Some (tr, cg) ->
cg' = apply tr cg -> 
length (G cg') = length (Transfos inp).
Proof. 
intros H H1 H2.
pose proof (H3 := onestep_length).
cbv zeta in H3. rewrite H in H1. 
specialize (H3 inp). rewrite H1 in H3.
rewrite <- H2 in H3. assumption.
Qed. 

Lemma first_transfo_applied_match inp'  :
match first_transfo_applied (Transfos inp') (CG inp') with
  | None => True
  | Some (tr, cg) => 
    first_transfo_applied (Transfos inp') (CG inp') = Some (tr, cg)
end.
Proof. 
destruct (first_transfo_applied (Transfos inp') (CG inp')).
destruct p as (tr, cg). reflexivity.
exact I.
Qed. 


(* onestep prepares the input, find the first transformation 
that can be applied, and applies it *)

Definition onestep (inp: input) : option input.
Proof.
pose (inp' := prepare inp).
destruct (first_transfo_applied (Transfos inp') (CG inp')) as [p |] eqn:E.
- destruct p as (tr, cg').
exact (let cg'' := apply tr cg' in Some
          ({| Transfos := Transfos inp;
             CG := cg'' ;
             inv := onestep_length2 inp inp' tr cg' cg'' eq_refl
                  E eq_refl
          |})).
- exact None.
Defined.

Definition block_trigger (n: nat) (cg: CoqGoal) : CoqGoal.
Proof. 
destruct cg as (hyps0, g0, inv0).
pose (hyps := seen_n_list n hyps0).
pose (g := seen_n n g0).
assert (H : forallb
     (same_length (seen_n n g0))
     (seen_n_list n hyps0) = true).
unfold same_length.
rewrite seen_n_length.
pose proof (H1 := seen_n_list_length).
eapply H1 in inv0. eassumption. 
exact ({| Hs := hyps; G := g ; samelength := H |}).
Defined.

Lemma block_trigger_length cg k : 
length (G (block_trigger k cg)) = length (G cg).
Proof.
destruct cg as (hyps, g, inv).
destruct k ; unfold block_trigger; destruct g ; simpl in *; try reflexivity.
rewrite seen_n_length. reflexivity.
Qed.

Lemma first_transfo_length inp tr cg cg' :
first_transfo_applied (Transfos inp) (CG inp) = Some (tr, cg') ->
length (G cg') = length (G cg) -> 
length (G cg') = length (Transfos inp).
Proof. 
intros H H1.
rewrite H1.
destruct inp as (trs, cg0, inv).
simpl in *.
pose proof (H2 := first_transfo_applied_length_goal).
unfold first_transfo_applied in H.
specialize (H2 trs cg0 0). rewrite H in H2.
rewrite <- inv. rewrite <- H2. rewrite <- H1. reflexivity. Qed.

Definition onestep_fuel (n: nat) (inp: input) : option input.
Proof.
destruct n eqn:En.
- pose (inp' := prepare inp).
destruct (first_transfo_applied (Transfos inp') (CG inp')) as [p |] eqn:E.
  * destruct p as (tr, cg'). pose (k := find (Transfos inp') tr).
refine (match (onestep {| Transfos := Transfos inp'; CG := block_trigger k cg'; 
inv := _ |}) with
| Some x => Some x 
| None => None
end). rewrite block_trigger_length.
pose proof (H := first_transfo_length).
specialize (H inp' tr (CG inp') cg').
apply H in E. apply E. simpl. unfold prepare in inp'.
rewrite <- prepare_steps_length2 with (trs := Transfos inp).
pose proof (H1 := first_transfo_applied_length_goal).
specialize (H1 (Transfos inp') (CG inp') 0).
unfold first_transfo_applied in E.
rewrite E in H1. unfold inp' in H1.
simpl in *. rewrite <- H1.
eapply prepare_steps_length2.
 * exact None.
- exact (onestep inp).
Defined.

Definition example_input1 :=
{| Transfos := [(GoalSensitive, ChangesHyps); (GoalSensitive, ChangesAll)];
   CG := {| Hs := [[false; false]; [false; false]; [false; false]]; 
            G := [false; false] ; 
            samelength := eq_refl |};
   inv := eq_refl |}.

Compute (onestep_fuel 0 example_input1).

(** Fuel for all transformations **) 


(* 1st integer : the number of the transformation
2nd integer : the remaining fuel she has 
*)

Inductive nat_inf :=
| Nat : nat -> nat_inf
| Infinity : nat_inf.

Definition fuel := list nat_inf.

Record input_fuel := mkInputFuel
{ In : input;
  Fuel : fuel
}.

(* Returns the index of the first transformation 
that could be applied *)

Fixpoint first_with_fuel_aux (f : fuel) (n1 : nat) : option nat :=
  match f with
    | [] => None 
    | n2 :: fs => 
      match n2 with
        | Infinity => Some n1
        | Nat 0 => first_with_fuel_aux fs (S n1)
        | Nat (S n3) => Some n1
      end
  end.

Lemma first_with_fuel_le f : 
forall n n', first_with_fuel_aux f n = Some n' -> n' >= n.
Proof.
induction f as [ | x f IHf] ; intros n n'.
  - destruct n as [ | n]; intro H ; inversion H.
  - destruct x as [ [ | x] | ]; simpl in *.
    * specialize (IHf (S n)). specialize (IHf n').
intro H. assert (H1 : n' >= S n). apply IHf.
assumption. unfold ">=" in *. apply le_S_n.
assert (H2 : n' <= S n'). apply Nat.le_succ_diag_r.
eapply Nat.le_trans. apply H1. apply H2. 
    * intro H. injection H. intro H2.
subst. unfold ">=". constructor.
    * intro H. injection H. intro H2.
subst. unfold ">=". constructor.
Qed.

Fixpoint first_transfo_applied_fuel_aux (n : nat) (f: fuel) (inp : input) (structarg : nat) :=
  match structarg with
    | 0 => None
    | S structarg' => 
        let opt := first_with_fuel_aux f n in
        match opt with
          | None => None
          | Some n' => 
              let tr := nth n' (Transfos inp) (AllSensitive, ChangesAll) in
                match check_trigger tr n' (CG inp) with
                  | None => 
                      let f' := List.skipn (S n') f in
                      first_transfo_applied_fuel_aux (S n') f' inp structarg'
                  | Some cg' => Some (tr, cg')
                end
          end
     end.

Print list_ind.

Lemma list_length_ind_aux (A : Type) (P : list A -> Prop) :
(forall l', (forall l, length l < length l' -> P l) -> P l') -> 
(forall (l' l : list A), length l' < length l -> P l').
Proof.
intros H l l' H1.
generalize dependent l.
induction l' as [ | x' l' IHl']; intros l.
- intros H2. inversion H2. 
- intros H2. simpl in H2. 
assert (Heq : length l = length l' \/ length l < length l') 
by lia. destruct Heq as [ Heq1 | Heq2]. apply H. rewrite Heq1.
apply IHl'. apply IHl'. assumption. Qed. 

Lemma list_length_ind (A : Type) (P : list A -> Prop) :
P [] -> (forall (l : list A), 
((forall (l' : list A), length l' < length l -> P l') -> P l)) -> 
forall l, P l.
Proof.
intros H H1 l.
induction l as [ | x xs IHxs].
- assumption. 
- pose proof (H2 := list_length_ind_aux).
apply H2 with (x :: x :: xs). assumption.
simpl. lia. Qed.

Definition first_transfo_applied_fuel f inp :=
  let structarg := length f in
  first_transfo_applied_fuel_aux 0 f inp structarg.
 
Lemma never_run_out_of_fuel_aux : 
forall f inp tr cg k,
(exists n, first_transfo_applied_fuel_aux k f inp n = Some (tr, cg)) ->
(forall leng, leng >= length f -> 
first_transfo_applied_fuel_aux k f inp leng = Some (tr, cg)).
Proof.
intro f.
apply list_length_ind with (P := 
fun f => forall inp tr cg k,
(exists n, first_transfo_applied_fuel_aux k f inp n = Some (tr, cg)) ->
(forall leng, leng >= length f -> first_transfo_applied_fuel_aux k f inp leng = Some (tr, cg))).
  - intros inp tr cg k H. destruct H as [n Hn]. simpl in Hn.
destruct n ; inversion Hn.
  - intros l H. intros inp tr cg k Hn leng Hleng. destruct Hn as [n Hn].
destruct (length l) as [ | len] eqn:E.
     * simpl in *. apply length_zero_iff_nil in E. subst. destruct n ; inversion  Hn. 
     * simpl in *. destruct (first_with_fuel_aux l k) as [n1 | ] eqn:E'.
        + destruct (check_trigger (nth n1 (Transfos inp) 
(AllSensitive, ChangesAll)) n1 (CG inp)) eqn:F. destruct leng as [ | leng'].
simpl. inversion Hleng. simpl. rewrite E'. rewrite F.
apply f_equal. destruct n. inversion Hn. simpl in Hn.
rewrite E' in Hn. rewrite F in Hn. inversion Hn; subst.
reflexivity.
destruct n. inversion Hn. simpl in Hn.
rewrite E' in Hn. rewrite F in Hn.
destruct l as [ | x l']; inversion E.
simpl in *. inversion E'. simpl in *. 
destruct x as [ [ | x'] | ] eqn:G.
assert (Hskip0 : length (skipn n1 l') < S (length l')) by 
(pose proof (Hskip := skipn_length);
specialize (Hskip nat_inf n1 l');
lia). 
assert (H' : forall (inp : input) (tr : transfo) (cg : CoqGoal) (k : nat),
(exists n : nat, first_transfo_applied_fuel_aux k (skipn n1 l') inp n =
Some (tr, cg)) ->
forall leng : nat,
leng >= length (skipn n1 l') ->
first_transfo_applied_fuel_aux k (skipn n1 l') inp leng =
Some (tr, cg)). apply H. lia. clear H.
assert (H2' : first_transfo_applied_fuel_aux (S n1) (skipn n1 l') inp
(length (skipn n1 l')) = Some (tr, cg) ->
first_transfo_applied_fuel_aux (S n1) (skipn n1 l') inp len =
Some (tr, cg)). intro H''.
eapply H'. exists n. assumption.
assert (Hn1 : n1 >= (S k)). apply first_with_fuel_le in E'.
apply E'. assert (Hnle : n1 >= 1). lia.
destruct n1 as [ | n1']. lia. 
pose proof (Hskip := skipn_length). 
specialize (Hskip nat_inf n1' l'). lia. destruct leng as [ | leng].
inversion Hleng. simpl in *. rewrite E'.
rewrite F. inversion E. apply H'. exists n.
assumption.
assert (Hlen' : len >= length (skipn n1 l')) by lia.
lia. destruct leng as [ | leng].
inversion Hleng. simpl in *. inversion E'; subst.
rewrite F. eapply H. 
pose proof (Hskip := skipn_length). 
specialize (Hskip nat_inf n1 l'). lia. exists n. assumption. 
assert (Hskip0 : length (skipn n1 l') <= (length l')) by 
(pose proof (Hskip := skipn_length);
specialize (Hskip nat_inf n1 l');
lia). lia. simpl. destruct leng as [ | leng].
inversion Hleng. simpl in *. inversion H2; subst. rewrite F.
apply H.
pose proof (Hskip := skipn_length). 
specialize (Hskip nat_inf n1 l'). lia.
exists n. assumption. 
pose proof (Hskip := skipn_length). 
specialize (Hskip nat_inf n1 l'). lia. 
 + destruct n. simpl in Hn. inversion Hn.
simpl in Hn. rewrite E' in Hn. inversion Hn.
Qed.

Lemma never_run_out_of_fuel : 
forall f inp tr cg,
(exists n, first_transfo_applied_fuel_aux 0 f inp n = Some (tr, cg)) ->
first_transfo_applied_fuel f inp = Some (tr, cg).
Proof.
unfold first_transfo_applied_fuel. intros.
eapply never_run_out_of_fuel_aux. assumption. lia. Qed.

Fixpoint onestep_input_fuel (inp : input_fuel) : option input :=
  match (Fuel inp) with
    | [] => None 
    | (n1, n2) :: ns =>
      match n2 with
        | Infinity => onestep inp
        | Nat n3 => 
          match n3 with
            | 0 => 
              let inp' := block_trigger n1 inp in
              onestep_input_fuel {| In := inp' ; Fuel := ns |}
            | S n4 => 
          end
      end
    end.


