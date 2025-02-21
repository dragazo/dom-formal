Axiom excl_mid : forall (p : Prop), p \/ ~p.
Axiom func_ext : forall (X Y : Type) (f g : X -> Y), (forall (x : X), f x = g x) -> f = g.
Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

(* ------------------------------------------------------------------------------------ *)

Theorem demorgan_and : forall (p q : Prop), ~(p /\ q) <-> (~p \/ ~q).
Proof. intros. destruct (excl_mid p), (excl_mid q); firstorder. Qed.

Theorem demorgan_or : forall (p q : Prop), ~(p \/ q) <-> (~p /\ ~q).
Proof. intros. destruct (excl_mid p), (excl_mid q); firstorder. Qed.
