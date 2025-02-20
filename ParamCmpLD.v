Require Import DomFormal.Graph.
Require Import DomFormal.Param.
Require Import DomFormal.Set.
Require Import DomFormal.Logic.

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

Definition orig_ld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), ~(D v) -> card_ge (cap (No v) D) 1) /\
    (forall (u v : V G), u <> v -> ~(D u) -> ~(D v) -> card_ge (sym (cap (No v) D) (cap (No u) D)) 1).
Definition orig_redld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), card_ge (cap (Nc v) D) 2) /\
    (forall (u v : V G), u <> v -> D v -> ~(D u) -> card_ge (sub (sym (cap (No v) D) (cap (No u) D)) (single v)) 1) /\
    (forall (u v : V G), u <> v -> ~(D v) -> ~(D u) -> card_ge (sym (cap (No v) D) (cap (No u) D)) 2).
Definition orig_detld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), card_ge (cap (Nc v) D) 2) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sym (cap (No v) D) (cap (No u) D)) 1) /\
    (forall (u v : V G), u <> v -> D u -> ~(D v) -> (card_ge (sub (cap (No v) D) (cap (No u) D)) 2 \/ card_ge (sub (cap (No u) D) (cap (No v) D)) 1)) /\
    (forall (u v : V G), u <> v -> ~(D u) -> ~(D v) -> (card_ge (sub (cap (No v) D) (cap (No u) D)) 2 \/ card_ge (sub (cap (No u) D) (cap (No v) D)) 2)).
Definition orig_errld {G : graph} (D : V G -> Prop) :=
    (forall (v : V G), card_ge (cap (Nc v) D) 3) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sub (sym (cap (No v) D) (cap (No u) D)) (cup (single v) (single u))) 1) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sub (sym (cap (No v) D) (cap (No u) D)) (single u)) 2) /\
    (forall (u v : V G), u <> v -> D u -> D v -> card_ge (sym (cap (No v) D) (cap (No u) D)) 3).

Theorem orig_ld_equiv : forall (G : graph) (D : V G -> Prop), ld D <-> orig_ld D.
Proof.
    unfold ld, orig_ld. repeat (split; intros).
    destruct H as [H _]. destruct (H v) as [x [H1 _]]. clear H. firstorder. rewrite H in H0. contradiction.
    destruct H as [_ H]. destruct (H u v H0) as [x [[H4 H5] _]]. firstorder; [rewrite H3 in H1 | rewrite H3 in H2]; contradiction.
    unfold closed_dominating. intros. destruct H as [H _]. destruct (excl_mid (D v)); firstorder.
    unfold self_distinguishing. intros. destruct H as [_ H]. destruct (excl_mid (D u)), (excl_mid (D v)); firstorder.
Qed.

Theorem orig_redld_equiv : forall (G : graph) (D : V G -> Prop), redld D <-> orig_redld D.
Proof.
    unfold redld, orig_redld. repeat (split; intros).

    destruct H as [H _]. firstorder.

    destruct H as [_ H]. destruct (H u v H0) as [x [[H3 H4] [y [[[H5 H6] H7] _]]]]. clear H.
    destruct (excl_mid (v = x /\ v = y)) as [[H8 H9] | H8]. rewrite <- H8 in H7. rewrite <- H9 in H7. firstorder.
    apply demorgan in H8. destruct H8 as [H8 | H8]; [exists x | exists y]; split; try reflexivity.
    destruct (excl_mid (x = u)) as [H9 | H9]. rewrite H9 in H4. contradiction. destruct H3 as [H3 | [H3 | H3]]; [| apply eq_sym in H3 |]; firstorder.
    destruct (excl_mid (y = u)) as [H9 | H9]. rewrite H9 in H6. contradiction. destruct H5 as [H5 | [H5 | H5]]; [| apply eq_sym in H5 |]; firstorder.

    destruct H as [_ H]. destruct (H u v H0) as [x [[H3 H4] [y [[[H5 H6] H7] _]]]]. clear H.
    exists x; split; [| exists y; split; try reflexivity].
    destruct H3 as [[[H31 H32] | [H31 H32]] | [H3 | H3]]; [| | rewrite H3 in H2 | rewrite H3 in H1]; firstorder.
    destruct H5 as [[[H51 H52] | [H51 H52]] | [H5 | H5]]; [| | rewrite H5 in H2 | rewrite H5 in H1]; firstorder.

    destruct H as [H _]. firstorder.

    unfold self_distinguishing. intros. destruct (excl_mid (D u)), (excl_mid (D v)).
    clear H. firstorder.
    destruct H as [_ [H _]]. destruct (H v u (not_eq_sym H0) H1 H2) as [x [H3 _]]. clear H. firstorder.
    destruct H as [_ [H _]]. destruct (H u v H0 H2 H1) as [x [H3 _]]. clear H. firstorder.
    destruct H as [_ [_ H]]. destruct (H u v H0 H2 H1) as [x [H3 [y [H4 _]]]]. clear H. firstorder.
Qed.

