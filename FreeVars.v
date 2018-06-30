Require Import Term.
Require Import Id.

(* Free variables of a term *)
Reserved Notation "x ?? e" (at level 0).
Inductive FV : term -> id -> Prop := 
    | FV_Var : forall (x : id), x ?? (Var x)
    | FV_App : forall (x : id) (t1 t2 : term), x ?? t1 \/ x ?? t2 -> x ?? (App t1 t2)
    | FV_Lam : forall (x y : id) (t : term), y ?? t /\ x <> y -> y ?? (Lam x t)
where "x ?? e" := (FV e x).
