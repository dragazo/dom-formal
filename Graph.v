Require Import DomFormal.Logic.
Require Import DomFormal.Set.

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
