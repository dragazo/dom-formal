(* ------------------------------------------------------------------------------------ *)

Axiom excl_mid : forall (p : Prop), p \/ ~p.
Axiom func_ext : forall (X Y : Type) (f g : X -> Y), (forall (x : X), f x = g x) -> f = g.
Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

(* ------------------------------------------------------------------------------------ *)

Definition universe {X : Type} : X -> Prop := fun (x : X) => True.
Definition empty {X : Type} : X -> Prop := fun (x : X) => False.

Definition single {X : Type} (x : X) : X -> Prop := fun (y : X) => x = y.

Definition subset {X : Type} (a b : X -> Prop) : Prop := forall (x : X), a x -> b x.

Definition cap {X : Type} (a b : X -> Prop) : X -> Prop := fun (x : X) => a x /\ b x.
Definition cup {X : Type} (a b : X -> Prop) : X -> Prop := fun (x : X) => a x \/ b x.
Definition sub {X : Type} (a b : X -> Prop) : X -> Prop := fun (x : X) => a x /\ ~(b x).
Definition sym {X : Type} (a b : X -> Prop) : X -> Prop := fun (x : X) => (a x /\ ~ b x) \/ (b x /\ ~ a x).

(* ------------------------------------------------------------------------------------ *)

Theorem subset_refl : forall (X : Type) (a : X -> Prop), subset a a.
Proof. firstorder. Qed.

Theorem subset_antisym : forall (X : Type) (a b : X -> Prop), subset a b -> subset b a -> a = b.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem subset_trans : forall (X : Type) (a b c : X -> Prop), subset a b -> subset b c -> subset a c.
Proof. firstorder. Qed.

(* ------------------------------------------------------------------------------------ *)

Theorem cap_self : forall (X : Type) (a : X -> Prop), cap a a = a.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem cap_comm : forall (X : Type) (a b : X -> Prop), cap a b = cap b a.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem cap_assoc : forall (X : Type) (a b c : X -> Prop), cap a (cap b c) = cap (cap a b) c.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem cap_subset_l : forall (X : Type) (a b : X -> Prop), subset (cap a b) a.
Proof. firstorder. Qed.

Theorem cap_subset_r : forall (X : Type) (a b : X -> Prop), subset (cap a b) b.
Proof. firstorder. Qed.

(* ------------------------------------------------------------------------------------ *)

Theorem cup_self : forall (X : Type) (a : X -> Prop), cup a a = a.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem cup_comm : forall (X : Type) (a b : X -> Prop), cup a b = cup b a.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem cup_assoc : forall (X : Type) (a b c : X -> Prop), cup a (cup b c) = cup (cup a b) c.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem cup_subset_l : forall (X : Type) (a b : X -> Prop), subset a (cup a b).
Proof. firstorder. Qed.

Theorem cup_subset_r : forall (X : Type) (a b : X -> Prop), subset b (cup a b).
Proof. firstorder. Qed.

(* ------------------------------------------------------------------------------------ *)

Theorem sub_self : forall (X : Type) (a : X -> Prop), sub a a = empty.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem sub_subset : forall (X : Type) (a b : X -> Prop), subset (sub a b) a.
Proof. firstorder. Qed.

(* ------------------------------------------------------------------------------------ *)

Theorem sym_self : forall (X : Type) (a : X -> Prop), sym a a = empty.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem sym_comm : forall (X : Type) (a b : X -> Prop), sym a b = sym b a.
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

Theorem sym_sub : forall (X : Type) (a b : X -> Prop), sym a b = cup (sub a b) (sub b a).
Proof. intros. apply func_ext. intros. apply prop_ext. firstorder. Qed.

(* ------------------------------------------------------------------------------------ *)

Fixpoint card_ge {X : Type} (a : X -> Prop) (k : nat) : Prop := match k with
    | 0 => True
    | S k' => exists (x : X), a x /\ card_ge (sub a (single x)) k'
end.

Definition card_le {X : Type} (a : X -> Prop) (k : nat) : Prop := ~ card_ge a (S k).

Definition card_eq {X : Type} (a : X -> Prop) (k : nat) : Prop := card_ge a k /\ card_le a k.

(* ------------------------------------------------------------------------------------ *)

Theorem card_subset : forall (X : Type) (a b : X -> Prop) (k : nat), subset a b -> card_ge a k -> card_ge b k.
Proof.
    intros. generalize dependent a. generalize dependent b. induction k. reflexivity. intros.
    destruct H0 as [x [H1 H2]]. exists x. split. exact (H x H1). firstorder.
Qed.

Theorem card_ge_S : forall (X : Type) (a b : X -> Prop) (k : nat), card_ge a (S k) -> card_ge a k.
Proof. intros. destruct H as [x [H1 H2]]. apply card_subset with (a := (sub a (single x))); firstorder. Qed.

(* ------------------------------------------------------------------------------------ *)

Record graph := {
    V : Type;
    E : V -> V -> Prop;
    E_nrefl : forall (v : V), ~ E v v;
    E_sym : forall (u v : V), E u v <-> E v u;
}.

Definition No {G : graph} (v : V G) := E G v.
Definition Nc {G : graph} (v : V G) := cup (No v) (single v).

(* ------------------------------------------------------------------------------------ *)

Definition open_dominated {G : graph} (k : nat) (D : V G -> Prop) (v : V G) :=
    card_ge (cap (No v) D) k.
Definition closed_dominated {G : graph} (k : nat) (D : V G -> Prop) (v : V G) :=
    card_ge (cap (Nc v) D) k.

Definition open_dominating {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (v : V G), open_dominated  k D v.
Definition closed_dominating {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (v : V G), closed_dominated  k D v.

(* ------------------------------------------------------------------------------------ *)

Definition open_distinguished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) :=
    card_ge (cap (sym (No u) (No v)) D) k.
Definition closed_distinguished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) :=
    card_ge (cap (sym (Nc u) (Nc v)) D) k.
Definition self_distinguished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) :=
    card_ge (cap (cup (sym (No u) (No v)) (cup (single u) (single v))) D) k.

Definition open_distinguishing {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (u v : V G), u <> v -> open_distinguished k D u v.
Definition closed_distinguishing {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (u v : V G), u <> v -> closed_distinguished k D u v.
Definition self_distinguishing {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (u v : V G), u <> v -> self_distinguished k D u v.

(* ------------------------------------------------------------------------------------ *)

Definition sharp_open_distinguished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) :=
    card_ge (cap (sub (No u) (No v)) D) k \/ card_ge (cap (sub (No v) (No u)) D) k.
Definition sharp_closed_distinguished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) :=
    card_ge (cap (sub (Nc u) (Nc v)) D) k \/ card_ge (cap (sub (Nc v) (Nc u)) D) k.
Definition sharp_self_distinguished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) :=
    card_ge (cap (cup (sub (No u) (No v)) (single u)) D) k \/ card_ge (cap (cup (sub (No v) (No u)) (single v)) D) k.

Definition sharp_open_distinguishing {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (u v : V G), u <> v -> sharp_open_distinguished k D u v.
Definition sharp_closed_distinguishing {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (u v : V G), u <> v -> sharp_closed_distinguished k D u v.
Definition sharp_self_distinguishing {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (u v : V G), u <> v -> sharp_self_distinguished k D u v.

(* ------------------------------------------------------------------------------------ *)

Definition odom {G : graph} (D : V G -> Prop) := open_dominating 1 D.
Definition old {G : graph} (D : V G -> Prop) := open_dominating 1 D /\ open_distinguishing 1 D.
Definition redold {G : graph} (D : V G -> Prop) := open_dominating 2 D /\ open_distinguishing 2 D.
Definition detold {G : graph} (D : V G -> Prop) := open_dominating 2 D /\ sharp_open_distinguishing 2 D.
Definition errold {G : graph} (D : V G -> Prop) := open_dominating 3 D /\ open_distinguishing 3 D.

Definition dom {G : graph} (D : V G -> Prop) := closed_dominating 1 D.
Definition ic {G : graph} (D : V G -> Prop) := closed_dominating 1 D /\ closed_distinguishing 1 D.
Definition redic {G : graph} (D : V G -> Prop) := closed_dominating 2 D /\ closed_distinguishing 2 D.
Definition detic {G : graph} (D : V G -> Prop) := closed_dominating 2 D /\ sharp_closed_distinguishing 2 D.
Definition erric {G : graph} (D : V G -> Prop) := closed_dominating 3 D /\ closed_distinguishing 3 D.

Definition ld {G : graph} (D : V G -> Prop) := closed_dominating 1 D /\ self_distinguishing 1 D.
Definition redld {G : graph} (D : V G -> Prop) := closed_dominating 2 D /\ self_distinguishing 2 D.
Definition detld {G : graph} (D : V G -> Prop) := closed_dominating 2 D /\ sharp_self_distinguishing 2 D.
Definition errld {G : graph} (D : V G -> Prop) := closed_dominating 3 D /\ self_distinguishing 3 D.

(* ------------------------------------------------------------------------------------ *)

Theorem old_is_odom : forall (G : graph) (D : V G -> Prop), old D -> odom D.
Proof. firstorder. Qed.

Theorem redold_is_old : forall (G : graph) (D : V G -> Prop), redold D -> old D.
Proof. firstorder. Qed.

Theorem detold_is_redold : forall (G : graph) (D : V G -> Prop), detold D -> redold D.
Proof.
    unfold detold, redold, sharp_open_distinguishing, open_distinguishing.
    intros. destruct H as [H1 H2]. split. exact H1. intros. apply (H2 u v) in H. firstorder.
Qed.

Theorem errold_is_detold : forall (G : graph) (D : V G -> Prop), errold D -> detold D.
Proof.
    unfold errold, detold, open_distinguishing, sharp_open_distinguishing.
    intros. destruct H as [H1 H2]. split. firstorder. intros. apply (H2 u v) in H.
    destruct H as [a [A H]]. destruct H as [b [B H]]. destruct H as [c [C H]]. clear H.
    unfold sharp_open_distinguished.

    rewrite sym_sub in A. rewrite sym_sub in B. rewrite sym_sub in C.
    destruct A as [[A | A] Da], B as [[[B | B] Db] Uab], C as [[[[C | C] Dc] Uac] Ubc].
    (* all: firstorder.

    left. firstorder. left. firstorder. left. firstorder. right. firstorder.
    left. firstorder. right. firstorder. right. firstorder. right. firstorder.
Qed. *)
