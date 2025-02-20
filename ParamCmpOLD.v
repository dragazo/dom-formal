Require Import DomFormal.Graph.
Require Import DomFormal.Param.
Require Import DomFormal.Set.

(* ------------------------------------------------------------------------------------ *)

Theorem old_is_odom : forall (G : graph) (D : V G -> Prop), old D -> odom D.
Proof. unfold old, odom. intros. destruct H as [H _]. exact H. Qed.

Theorem old_is_ld : forall (G : graph) (D : V G -> Prop), old D -> ld D.
Proof. unfold old, ld. intros. destruct H as [H1 H2]. split. clear H2. firstorder. clear H1. firstorder. Qed.

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
