Require Import DomFormal.Graph.
Require Import DomFormal.Param.
Require Import DomFormal.Set.

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
    destruct H as [H _]. unfold closed_dominating in H. destruct (H v) as [x H1]. clear H.

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
    