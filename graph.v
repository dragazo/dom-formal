Require Import Arith.
Require Import Bool.
Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------------------------ *)

Record ssetoid := {
    T : Type;
    T_eqb : T -> T -> bool;
    T_eqb_eq : forall (a b : T), T_eqb a b = true <-> a = b;
}.

Fixpoint filter {X : ssetoid} (f : T X -> bool) (l : list (T X)) : list (T X) := match l with
    | nil => nil
    | h :: t => if f h then h :: (filter f t) else (filter f t)
end.

Fixpoint contains {X : ssetoid} (l : list (T X)) (v : T X) : bool := match l with
    | nil => false
    | h :: t => if T_eqb X h v then true else contains t v
end.

Fixpoint distinct {X : ssetoid} (l : list (T X)) : bool := match l with
    | nil => true
    | h :: t => (negb (contains t h)) && distinct t
end.

(* ------------------------------------------------------------------------------------ *)

Theorem filter_predicate : forall (X : ssetoid) (l : list (T X)) (f : T X -> bool) (v : T X),
    contains (filter f l) v = true -> f v = true.
Proof.
    intros. induction l. all: simpl in H. discriminate H. destruct (f a) eqn:Ef.
    simpl in H. destruct (T_eqb X a v) eqn:Q. apply (T_eqb_eq X) in Q. rewrite <- Q. exact Ef. all: exact (IHl H).
Qed.

Theorem filter_subset : forall (X : ssetoid) (l : list (T X)) (f : T X -> bool) (v : T X),
    contains (filter f l) v = true -> contains l v = true.
Proof.
    intros. induction l. simpl in H. discriminate H. simpl. destruct (T_eqb X a v) eqn:Tav. reflexivity. apply IHl.
    simpl in H. destruct (f a) eqn:Efa. simpl in H. rewrite Tav in H. all: exact H.
Qed.

Theorem distinct_subset : forall (X : ssetoid) (l : list (T X)) (f : T X -> bool),
    distinct l = true -> distinct (filter f l) = true.
Proof.
    intros. unfold distinct. destruct (filter f l) eqn:fl. reflexivity. rewrite andb_true_iff. split.

    intros. induction l. reflexivity. simpl in H. rewrite andb_true_iff in H. destruct H as [H1 H2]. apply IHl in H2. clear IHl.
    simpl. destruct (f a) eqn:fa. simpl. rewrite andb_true_iff. split. all: try exact H2.
    
    


    induction l. reflexivity. intros. simpl. destruct (f a) eqn:fa. simpl. rewrite Bool.andb_true_iff. split.

    
    intros. induction l. reflexivity. simpl. destruct (f a) eqn:fa. simpl.

(* ------------------------------------------------------------------------------------ *)


Theorem distinct_filter : forall (X : Type) (eqb : X -> X -> bool)

Definition intersect {X : Type} (eqb : X -> X -> bool) (a b : list X) : list X := filter (contains eqb b) a.

Theorem intersect_refl : forall (X : Type) (eqb : X -> X -> bool) (a : list X), intersect eqb a a = a.
Proof.
    intros. unfold intersect.

Theorem intersect_contains : forall (X : Type) (eqb : X -> X -> bool) (a b : list X),
    contains eqb (intersect 

Definition bxor (p q : bool) := match p, q with
    | true, true => false
    | false, false => false
    | true, false => true
    | false, true => true
end.

(* ------------------------------------------------------------------------------------ *)

Record graph := {
    V : Type;
    V_eqb : V -> V -> bool;
    V_eqb_eq : forall (u v : V), V_eqb u v = true <-> u = v;

    E : V -> V -> bool;
    E_nrefl : forall (v : V), E v v = false;
    E_sym : forall (u v : V), E u v = E v u;

    N_open : V -> list V;
    N_open_distinct : forall (v : V), distinct V_eqb (N_open v) = true;
    N_open_adj : forall (u v : V), contains V_eqb (N_open v) u = true -> E u v = true;
}.

Definition N_closed (G : graph) (v : V G) := v :: N_open G v.

Theorem N_open_nrefl : forall (G : graph) (v : V G), contains (V_eqb G) (N_open G v) v = false.
Proof.
    intros. destruct (contains (V_eqb G) (N_open G v) v) eqn:H. all: try reflexivity.
    apply (N_open_adj G v v) in H. remember (E_nrefl G v). rewrite e in H. discriminate H.
Qed.

Theorem adj_neq : forall (G : graph) (u v : V G), E G u v = true -> u <> v.
Proof.
    unfold not. intros. rewrite H0 in H. remember (E_nrefl G v). rewrite e in H. discriminate H.
Qed.

(* ------------------------------------------------------------------------------------ *)

Definition k_closed_dom (G : graph) (D : V G -> bool) (k : nat) :=
    forall (v : V G), length (filter D (N_closed G v)) <? k = false.

Definition k_closed_disty (G : graph) (D : V G -> bool) (k : nat) :=
    forall (u v : V G), u <> v -> filter (fun x => D x && (contains (V_eqb G) N_
