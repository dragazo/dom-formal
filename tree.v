Require Import List.
Require Import Arith.
Require Import Bool.
Import ListNotations.

(* ------------------- *)
(* -- helper lemmas -- *)
(* ------------------- *)

Lemma bool_neq_eq : forall (b1 b2 : bool), b1 <> b2 <-> b1 = negb b2.
Proof.
    intros. destruct b1, b2. all: simpl; split; intros; try unfold not; intros.
    all: try discriminate H0. all: try reflexivity. all: try discriminate H.
    assert (true = true). reflexivity. apply H in H0. destruct H0.
    assert (false = false). reflexivity. apply H in H0. destruct H0.
Qed.

Lemma bool_contrapositive : forall (b1 b2 b3 b4 : bool), (b1 = b2 -> b3 = b4) -> (b3 <> b4 -> b1 <> b2).
Proof.
    intros. unfold not. intros. apply H in H1. apply H0 in H1. exact H1.
Qed.

Lemma leb_0 : forall (x : nat), x <=? 0 = true -> x =? 0 = true.
Proof.
    intros. destruct x eqn:Ex. reflexivity. simpl in H. discriminate H.
Qed.

Lemma leb_S : forall (x y : nat), x <=? y = true -> x <=? S y = true.
Proof.
    induction x. all: intros; simpl. reflexivity.
    destruct y eqn:Ey. apply leb_0 in H. rewrite Nat.eqb_eq in H. discriminate H.
    apply IHx. simpl in H. exact H.
Qed.

Lemma leb_P : forall (x y : nat), x <=? S y = false -> x <=? y = false.
Proof.
    induction x. all: intros; simpl. simpl in H. discriminate H.
    destruct y eqn:Ey. reflexivity. apply IHx. simpl in H. exact H.
Qed.

Lemma leb_SS : forall (n m : nat), (S n <=? S m) = (n <=? m).
Proof.
    destruct m. all: reflexivity.
Qed.

Lemma nleb_S : forall (n : nat), S n <=? n = false.
Proof.
    induction n. reflexivity. rewrite leb_SS. exact IHn.
Qed.

Lemma leb_neqb_Sn : forall (a b : nat), a <=? S b = true -> a =? S b = false -> a <=? b = true.
Proof.
    induction a. reflexivity.
    intros. destruct b eqn:Eb. simpl in H. apply leb_0 in H. rewrite Nat.eqb_eq in H. rewrite H in H0. simpl in H0. discriminate H0.
    simpl. simpl in H. simpl in H0. exact (IHa n H H0).
Qed.

(* ---------------------- *)
(* -- helper functions -- *)
(* ---------------------- *)

Definition range (n : nat) : list nat :=
    let fix range_impl (m : nat) : list nat := match m with
        | 0 => nil
        | S m' => (n - m) :: (range_impl m')
    end in range_impl n.

Fixpoint filter {X : Type} (f : X -> bool) (l : list X) : list X := match l with
    | nil => nil
    | h :: t => if f h then h :: (filter f t) else (filter f t)
end.

Fixpoint contains {X : Type} (eqb : X -> X -> bool) (l : list X) (v : X) : bool := match l with
    | nil => false
    | h :: t => if eqb h v then true else contains eqb t v
end.

(* ----------------------- *)
(* -- tree construction -- *)
(* ----------------------- *)

Inductive tree : nat -> Type :=
    | singleton : tree 0
    | addition (n : nat) (t : tree n) (p : nat) : p <=? n = true -> tree (S n)
    .

(* -------------------- *)
(* -- tree adjacency -- *)
(* -------------------- *)

Fixpoint adjacent (n : nat) (t : tree n) (v1 v2 : nat) : bool := match t with
    | singleton => false
    | addition n' t' p' _ => ((v1 =? S n) && (v2 =? p')) || ((v2 =? S n) && (v1 =? p')) || adjacent n' t' v1 v2
end.

Theorem adjacent_sym : forall (n : nat) (t : tree n) (v1 v2 : nat), adjacent n t v1 v2 = adjacent n t v2 v1.
Proof.
    induction t. all: intros; simpl. reflexivity. rewrite (orb_comm (_ && _) _). rewrite IHt. reflexivity.
Qed.

Theorem adjacent_nrefl : forall (n : nat) (t : tree n) (v : nat), adjacent n t v v = false.
Proof.
    induction t. all: intros; simpl. reflexivity. rewrite IHt. destruct (v =? S (S n)) eqn:E1, (v =? p) eqn:E2. all: try reflexivity.
    rewrite Nat.eqb_eq in E1. rewrite Nat.eqb_eq in E2. rewrite E2 in E1.
    assert (p <=? n = false). rewrite E1.
    assert (forall (x : nat), S (S x) <=? x = false). induction x. reflexivity.
    assert ((S (S (S x)) <=? S x) = (S (S x) <=? x)). reflexivity. rewrite H. exact IHx.
    exact (H n). rewrite H in e. discriminate e.
Qed.

Theorem adjacent_exterior : forall (n : nat) (t : tree n) (v1 v2 : nat), v1 <=? S n = false -> adjacent n t v1 v2 = false.
Proof.
    induction t. all: intros; simpl. reflexivity.
    destruct ((v1 =? S (S n)) && (v2 =? p)) eqn:E1.
    rewrite andb_true_iff in E1. destruct E1 as [E11 E12].
    rewrite Nat.eqb_eq in E11. rewrite E11 in H. simpl in H. rewrite Nat.leb_refl in H. discriminate H.
    simpl. destruct ((v2 =? S (S n)) && (v1 =? p)) eqn:E2.
    rewrite andb_true_iff in E2. destruct E2 as [E21 E22].
    rewrite Nat.eqb_eq in E22. rewrite <- E22 in e. apply leb_S in e. apply leb_S in e. rewrite e in H. discriminate H.
    simpl. apply IHt. apply leb_P in H. exact H.
Qed.

Theorem adjacent_interior : forall (n : nat) (t : tree n) (v1 v2 : nat), adjacent n t v1 v2 = true -> v1 <=? S n = true /\ v2 <=? S n = true.
Proof.
    assert (forall (n' : nat) (t' : tree n') (v1' v2' : nat), adjacent n' t' v1' v2' = true -> v1' <=? S n' = true).
    intros. remember (bool_contrapositive _ _ _ _ (adjacent_exterior n' t' v1' v2')) as E. clear HeqE.
    repeat rewrite bool_neq_eq in E. simpl in E. exact (E H).
    split. exact (H n t v1 v2 H0). rewrite adjacent_sym in H0. exact (H n t v2 v1 H0).
Qed.

Theorem adjacent_ntrans : forall (n : nat) (t : tree n) (v1 v2 v3 : nat), adjacent n t v1 v2 = true -> adjacent n t v2 v3 = true -> v1 =? v3 = false -> adjacent n t v1 v3 = false.
Proof.
    induction t. all: intros; simpl. reflexivity.
    destruct (v1 =? v2) eqn:Ev12. rewrite Nat.eqb_eq in Ev12. rewrite Ev12 in H. rewrite adjacent_nrefl in H. discriminate H.
    destruct (v2 =? v3) eqn:Ev23. rewrite Nat.eqb_eq in Ev23. rewrite Ev23 in H0. rewrite adjacent_nrefl in H0. discriminate H0.
    inversion H. inversion H0. clear H. clear H0.

    destruct ((v1 =? S (S n)) && (v3 =? p)) eqn:E1. rewrite andb_true_iff in E1. destruct E1 as [E11 E12].
    rewrite Nat.eqb_eq in E11. rewrite Nat.eqb_eq in E12.
    rewrite <- E11 in H3. rewrite <- E12 in H3. rewrite Ev23 in H3. rewrite H1 in H3.
    repeat rewrite andb_false_r in H3. simpl in H3.
    apply adjacent_interior in H3. destruct H3 as [H31 H32]. rewrite E11 in H31.
    rewrite nleb_S in H31. discriminate H31.

    destruct ((v3 =? S (S n)) && (v1 =? p)) eqn:E2. rewrite andb_true_iff in E2. destruct E2 as [E21 E22].
    rewrite Nat.eqb_eq in E21. rewrite Nat.eqb_eq in E22.
    rewrite <- E21 in H4. rewrite <- E22 in H4. rewrite (Nat.eqb_sym v2 v1) in H4. rewrite Ev23 in H4. rewrite Ev12 in H4.
    rewrite andb_false_r in H4. simpl in H4.
    apply adjacent_interior in H4. destruct H4 as [H41 H42]. rewrite E21 in H42.
    rewrite nleb_S in H42. discriminate H42.

    simpl. destruct (adjacent n t v1 v3) eqn:adj13. all: try reflexivity.
    destruct (adjacent n t v1 v2) eqn:adj12. clear H3.
    rewrite adjacent_sym in adj12. rewrite (IHt v2 v1 v3 adj12 adj13 Ev23) in H4. rename H4 into H3.
    all: rewrite orb_false_r in H3; rewrite orb_true_iff in H3; repeat rewrite andb_true_iff in H3; destruct H3 as [[H31 H32]|[H31 H32]]; rewrite Nat.eqb_eq in H31; rewrite Nat.eqb_eq in H32.
    apply adjacent_interior in adj12. destruct adj12 as [adj12 _]. rewrite H31 in adj12. rewrite nleb_S in adj12. discriminate adj12.
    apply adjacent_interior in adj13. destruct adj13 as [_ adj13]. rewrite H31 in adj13. rewrite nleb_S in adj13. discriminate adj13.
    apply adjacent_interior in adj13. destruct adj13 as [adj13 _]. rewrite H31 in adj13. rewrite nleb_S in adj13. discriminate adj13.
    rewrite <- H31 in H4. rewrite <- H32 in H4. rewrite (Nat.eqb_sym v3 v1) in H4. rewrite (Nat.eqb_sym v2 v1) in H4.
    rewrite H1 in H4. rewrite Ev12 in H4. repeat rewrite andb_false_r in H4. simpl in H4.
    apply adjacent_interior in H4. destruct H4 as [H4 _]. rewrite H31 in H4. rewrite nleb_S in H4. discriminate H4.
Qed.

(* ------------------------ *)
(* -- tree neighborhoods -- *)
(* ------------------------ *)

Definition neighborhood (n : nat) (t : tree n) (v : nat) : list nat := filter (fun u => adjacent n t u v) (range (S (S n))).
Definition degree (n : nat) (t : tree n) (v : nat) : nat := length (neighborhood n t v).

Theorem neighborhood_adjacent : forall (n : nat) (t : tree n) (u v : nat), (contains (fun a b => a =? b) (neighborhood n t u) v) = adjacent n t u v.
Proof.
    induction t. all: intros; simpl. reflexivity.
    destruct (neighborhood (S n) (addition n t p e) u) eqn:Env. simpl.
    destruct ((u =? S (S n)) && (v =? p)) eqn:E1. rewrite andb_true_iff in E1. destruct E1 as [E11 E12].
    apply Nat.eqb_eq in E11. apply Nat.eqb_eq in E12.

Theorem neighborhood_nrefl : forall (n : nat) (t : tree n) (v : nat), (contains (fun a b => a =? b) (neighborhood n t v) v) = false.
Proof.
    assert (forall (n' : nat) (t' : tree n') (v' : nat) (l' : list nat), neighborhood n' t' v' = v' :: l' -> False).
    induction t'. intros. unfold neighborhood in H. simpl in H. discriminate H.
    intros. destruct (neighborhood (S n) (addition n t' p e) v') eqn:Env'. discriminate H.
    inversion H. clear H. rewrite H1 in Env'. rewrite H2 in Env'. apply (IHt' v' l').
    rewrite <- Env'.

    induction t. all: intros; simpl. reflexivity.
    destruct (neighborhood (S n) (addition n t p e) v) eqn:Env. reflexivity.
    simpl. destruct (n0 =? v) eqn:En0v. rewrite Nat.eqb_eq in En0v.
    rewrite En0v in Env.




    unfold contains. destruct (neighborhood (S n) (addition n t p e) v) eqn:Env. reflexivity.
    destruct (n0 =? v) eqn:En0v.