Require Import DomFormal.Graph.
Require Import DomFormal.Set.

(* ------------------------------------------------------------------------------------ *)

Definition open_dominated {G : graph} (k : nat) (D : V G -> Prop) (v : V G) :=
    card_ge (cap (No v) D) k.
Definition closed_dominated {G : graph} (k : nat) (D : V G -> Prop) (v : V G) :=
    card_ge (cap (Nc v) D) k.

Definition open_dominating {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (v : V G), open_dominated k D v.
Definition closed_dominating {G : graph} (k : nat) (D : V G -> Prop) :=
    forall (v : V G), closed_dominated k D v.

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
