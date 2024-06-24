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
Definition sym {X : Type} (a b : X -> Prop) : X -> Prop := fun (x : X) => (a x /\ ~(b x)) \/ (~(a x) /\ b x).

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

(* ------------------------------------------------------------------------------------ *)

Fixpoint card_ge {X : Type} (a : X -> Prop) (k : nat) : Prop := match k with
    | 0 => True
    | S k' => exists (x : X), a x /\ card_ge (sub a (single x)) k'
end.

(* ------------------------------------------------------------------------------------ *)

Theorem card_subset : forall (X : Type) (a b : X -> Prop) (k : nat), subset a b -> card_ge a k -> card_ge b k.
Proof.
    intros. generalize dependent a. generalize dependent b. induction k. reflexivity. intros.
    destruct H0 as [x [H1 H2]]. exists x. split. exact (H x H1). firstorder.
Qed.

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

Definition open_dominated {G : graph} (k : nat) (D : V G -> Prop) (v : V G) := card_ge (cap (No v) D) k.
Definition closed_dominated {G : graph} (k : nat) (D : V G -> Prop) (v : V G) := card_ge (cap (Nc v) D) k.

Definition open_dominating {G : graph} (k : nat) (D : V G -> Prop) := forall (v : V G), open_dominated  k D v.
Definition closed_dominating {G : graph} (k : nat) (D : V G -> Prop) := forall (v : V G), closed_dominated  k D v.

(* ------------------------------------------------------------------------------------ *)

Definition open_distingished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) := card_ge (cap (sym (No u) (No v)) D) k.
Definition closed_distingished {G : graph} (k : nat) (D : V G -> Prop) (u v : V G) := card_ge (cap (sym (Nc u) (Nc v)) D) k.

Definition open_distinguishing {G : graph} (k : nat) (D : V G -> Prop) := forall (u v : V G), open_distingished k D u v.
Definition closed_distinguishing {G : graph} (k : nat) (D : V G -> Prop) := forall (u v : V G), closed_distingished k D u v.

(* ------------------------------------------------------------------------------------ *)

