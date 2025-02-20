Require Import DomFormal.Graph.
Require Import DomFormal.Param.
Require Import DomFormal.Set.

(* ------------------------------------------------------------------------------------ *)

Theorem ic_is_dom : forall (G : graph) (D : V G -> Prop), ic D -> dom D.
Proof. unfold ic, dom. intros. destruct H as [H _]. exact H. Qed.

Theorem ic_is_ld : forall (G : graph) (D : V G -> Prop), ic D -> ld D.
Proof. unfold ic, ld. intros. destruct H as [H1 H2]. split. exact H1. clear H1. firstorder. Qed.

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
