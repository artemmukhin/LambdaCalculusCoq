Require Import Id.

(* Lambda term definition *)
Inductive term : Type :=
    | Var : id -> term
    | App : term -> term -> term
    | Lam : id -> term -> term.

Definition x := (Id 1).
Definition y := (Id 2).
Definition z := (Id 3).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.
