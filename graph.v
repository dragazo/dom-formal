(* ------------------------------------------------------------------------------------ *)

Axiom excl_mid : forall (p : Prop), p \/ ~p.
Axiom func_ext : forall (X Y : Type) (f g : X -> Y), (forall (x : X), f x = g x) -> f = g.
Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

(* ------------------------------------------------------------------------------------ *)

Theorem demorgan : forall (p q : Prop), ~(p /\ q) <-> (~p \/ ~q).
Proof. intros. destruct (excl_mid p), (excl_mid q); firstorder. Qed.

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

Definition min_deg (G : graph) (k : nat) : Prop := forall (v : V G), card_ge (No v) k.
Definition max_deg (G : graph) (k : nat) : Prop := forall (v : V G), card_le (No v) k.

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
Proof. unfold old, odom. intros. destruct H as [H _]. exact H. Qed.

Theorem redold_is_old : forall (G : graph) (D : V G -> Prop), redold D -> old D.
Proof. unfold redold, old. intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. firstorder. Qed.

Theorem detold_is_redold : forall (G : graph) (D : V G -> Prop), detold D -> redold D.
Proof.
    unfold detold, redold, sharp_open_distinguishing, open_distinguishing.
    intros. destruct H as [H1 H2]. split. exact H1. clear H1. intros. apply (H2 u v) in H. clear H2. firstorder.
Qed.

Theorem errold_is_detold : forall (G : graph) (D : V G -> Prop), errold D -> detold D.
Proof.
    unfold errold, detold, open_distinguishing, sharp_open_distinguishing, sharp_open_distinguished.
    intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. intros. apply (H2 u v) in H. clear H2.
    destruct H as [a [A H]]. destruct H as [b [B H]]. destruct H as [c [C _]].
    rewrite sym_sub in A. rewrite sym_sub in B. rewrite sym_sub in C.
    destruct A as [[A | A] Da], B as [[[B | B] Db] Uab], C as [[[[C | C] Dc] Uac] Ubc].
    all: firstorder.
Qed.

(* ------------------------------------------------------------------------------------ *)

Theorem ic_is_dom : forall (G : graph) (D : V G -> Prop), ic D -> dom D.
Proof. unfold ic, dom. intros. destruct H as [H _]. exact H. Qed.

Theorem redic_is_ic : forall (G : graph) (D : V G -> Prop), redic D -> ic D.
Proof. unfold redic, ic. intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. firstorder. Qed.

Theorem detic_is_redic : forall (G : graph) (D : V G -> Prop), detic D -> redic D.
Proof.
    unfold detic, redic, sharp_closed_distinguishing, closed_distinguishing.
    intros. destruct H as [H1 H2]. split. exact H1. clear H1. intros. apply (H2 u v) in H. clear H2. firstorder.
Qed.

Theorem erric_is_detic : forall (G : graph) (D : V G -> Prop), erric D -> detic D.
Proof.
    unfold erric, detic, closed_distinguishing, sharp_closed_distinguishing, sharp_closed_distinguished.
    intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. intros. apply (H2 u v) in H. clear H2.
    destruct H as [a [A H]]. destruct H as [b [B H]]. destruct H as [c [C _]].
    rewrite sym_sub in A. rewrite sym_sub in B. rewrite sym_sub in C.
    destruct A as [[A | A] Da], B as [[[B | B] Db] Uab], C as [[[[C | C] Dc] Uac] Ubc].
    all: firstorder.
Qed.

(* ------------------------------------------------------------------------------------ *)

Theorem ld_is_dom : forall (G : graph) (D : V G -> Prop), ld D -> dom D.
Proof. unfold ld, dom. intros. destruct H as [H _]. exact H. Qed.

Theorem redld_is_ld : forall (G : graph) (D : V G -> Prop), redld D -> ld D.
Proof. unfold redld, ld. intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. firstorder. Qed.

Theorem detld_is_redld : forall (G : graph) (D : V G -> Prop), detld D -> redld D.
Proof.
    unfold detld, redld, sharp_self_distinguishing, self_distinguishing.
    intros. destruct H as [H1 H2]. split. exact H1. clear H1. intros. apply (H2 u v) in H. clear H2. firstorder.
Qed.

Theorem errld_is_detld : forall (G : graph) (D : V G -> Prop), errld D -> detld D.
Proof.
    unfold errld, detld, self_distinguishing, sharp_self_distinguishing, sharp_self_distinguished.
    intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. intros. apply (H2 u v) in H. clear H2.
    destruct H as [a [A H]]. destruct H as [b [B H]]. destruct H as [c [C _]].
    rewrite sym_sub in A. rewrite sym_sub in B. rewrite sym_sub in C.
    destruct A as [[A | A] Da], B as [[[B | B] Db] Uab], C as [[[[C | C] Dc] Uac] Ubc].
    all: firstorder.
Qed.

(* ------------------------------------------------------------------------------------ *)

Theorem old_is_ld : forall (G : graph) (D : V G -> Prop), old D -> ld D.
Proof. unfold old, ld. intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. firstorder. Qed.

Theorem ic_is_ld : forall (G : graph) (D : V G -> Prop), ic D -> ld D.
Proof. unfold ic, ld. intros. destruct H as [H1 H2]. split. exact H1. clear H1. firstorder. Qed.

(* ------------------------------------------------------------------------------------ *)

Definition previous_ld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), ~(D v) -> card_ge (cap (No v) D) 1) /\
    (forall (u v : V G), u <> v -> ~(D u) -> ~(D v) -> card_ge (sym (cap (No v) D) (cap (No u) D)) 1).
Definition previous_redld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), card_ge (cap (Nc v) D) 2) /\
    (forall (u v : V G), u <> v -> D v -> ~(D u) -> card_ge (sub (sym (cap (No v) D) (cap (No u) D)) (single v)) 1) /\
    (forall (u v : V G), u <> v -> ~(D v) -> ~(D u) -> card_ge (sym (cap (No v) D) (cap (No u) D)) 2).
Definition previous_detld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), card_ge (cap (Nc v) D) 2) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sym (cap (No v) D) (cap (No u) D)) 1) /\
    (forall (u v : V G), u <> v -> D u -> ~(D v) -> (card_ge (sub (cap (No v) D) (cap (No u) D)) 2 \/ card_ge (sub (cap (No u) D) (cap (No v) D)) 1)) /\
    (forall (u v : V G), u <> v -> ~(D u) -> ~(D v) -> (card_ge (sub (cap (No v) D) (cap (No u) D)) 2 \/ card_ge (sub (cap (No u) D) (cap (No v) D)) 2)).
Definition previous_errld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), card_ge (cap (Nc v) D) 3) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sub (sym (cap (No v) D) (cap (No u) D)) (cup (single v) (single u))) 1) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sub (sym (cap (No v) D) (cap (No u) D)) (single u)) 2) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sym (cap (No v) D) (cap (No u) D)) 3).

Theorem previous_ld_equiv : forall (G : graph) (D : V G -> Prop), ld D <-> previous_ld D.
Proof.
    unfold ld, previous_ld. repeat (split; intros).
    destruct H as [H _]. unfold closed_dominating in H. remember (H v) as H1.

    (* unfold ld, previous_ld. repeat (split; intros).
    destruct H as [H _]. destruct (H v) as [x [[H1 H2] _]]. clear H. firstorder. rewrite H in H0. firstorder.
    destruct H as [_ H]. destruct (H u v0 H1) as [x [H4 _]]. clear H. firstorder; [rewrite H in H2 | rewrite H in H3]; firstorder.
    unfold closed_dominating. intros. remember (H v) as H1. clear HeqH1. clear H. destruct (excl_mid (D v)); firstorder.
    unfold self_distinguishing. intros. destruct (excl_mid (D u)), (excl_mid (D v)); firstorder. destruct (H v H2) as [_ H3]. clear H. firstorder.
Qed.

Theorem previous_redld_equiv : forall (G : graph) (D : V G -> Prop), redld D <-> previous_redld D.
Proof.
    unfold redld, previous_redld. repeat (split; intros).

    destruct H as [H _]. firstorder.

    destruct H as [_ H]. destruct (H u v0 H0) as [x [[H3 H4] [y [[[H5 H6] H7] _]]]]. clear H.
    destruct (excl_mid (v0 = x /\ v0 = y)) as [[H8 H9] | H8]. rewrite <- H8 in H7. rewrite <- H9 in H7. firstorder.
    apply demorgan in H8. destruct H8 as [H8 | H8]; [exists x | exists y]; split; try reflexivity. split; try exact H8.
    destruct (excl_mid (x = u)) as [H9 | H9]. rewrite H9 in H4. firstorder. destruct H3 as [H3 | [H3 | H3]]; [| apply eq_sym in H3 |]; firstorder.
    destruct (excl_mid (y = u)) as [H9 | H9]. rewrite H9 in H6. firstorder. destruct H5 as [H5 | [H5 | H5]]; [| apply eq_sym in H5 |]; firstorder.

    destruct H as [_ H]. destruct (H u0 v1 H3) as [x [[H6 H7] [y [[[H8 H9] H10] _]]]]. clear H.
    exists x; split; [| exists y; split; try reflexivity].
    destruct H6 as [[[H61 H62] | [H61 H62]] | [H6 | H6]]; [| | rewrite H6 in H5 | rewrite H6 in H4]; firstorder.
    destruct H8 as [[[H81 H82] | [H81 H82]] | [H8 | H8]]; [| | rewrite H8 in H5 | rewrite H8 in H4]; firstorder.

    unfold closed_dominating. intros. destruct (H v) as [H1 _]. clear H. firstorder.

    unfold self_distinguishing, self_distinguished. intros. destruct (H u) as [_ [H2 H2']]. clear H.
    destruct (excl_mid (D u)) as [Hu | Hu], (excl_mid (D v)) as [Hv | Hv]. firstorder.
    destruct (H2 v u (not_eq_sym H0) Hu Hv) as [H3 H4]. clear H2. firstorder.
    destruct (H2 u v H0 Hv Hu) as [H3 H4]. clear H2. firstorder. *)
    


    

    (* unfold self_distinguishing, self_distinguished. intros. destruct (H u) as [Hd H2]. clear H.
    destruct (excl_mid (D u)) as [Hu | Hu], (excl_mid (D v)) as [Hv | Hv]. clear Hd. firstorder.
    destruct (H2 v u (not_eq_sym H0) Hu Hv) as [H3 H4]. clear H2. clear Hd. firstorder.
    destruct (H2 u v H0 Hv Hu) as [H3 H4]. clear H2. clear Hd. firstorder.
    
    destruct Hd as [x [Hd1 [y [Hd2 _]]]].
    firstorder. *)
    
