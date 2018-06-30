Require Import Term.
Require Import Id.

(* Free variables of a term *)
Reserved Notation "x ?? e" (at level 0).
Inductive FV : term -> id -> Prop := 
    | FV_Var : forall (x : id), x ?? (Var x)
    | FV_App : forall (x : id) (t1 t2 : term), x ?? t1 \/ x ?? t2 -> x ?? (App t1 t2)
    | FV_Lam : forall (x y : id) (t : term), y ?? t -> x <> y -> y ?? (Lam x t)
where "x ?? e" := (FV e x).

Lemma FV_Var_other1 : forall x y, x <> y -> not x ?? (Var y).
Proof.
  intros.
  unfold not. intros.
  inversion H0. auto.
Qed.

Lemma FV_Var_other2 : forall x y, not x ?? (Var y) -> x <> y.
Proof.
  intros.
  unfold not. intros. subst.
  assert (y ?? (Var y)) by constructor.
  auto.
Qed.

Lemma FV_App_not1 : forall A B x, not x ?? (App A B) -> not x ?? A.
Proof.
  intros. unfold not. intros.
  assert (x ?? (App A B)). { constructor. auto. } auto.
Qed.

Lemma FV_App_not2 : forall A B x, not x ?? (App A B) -> not x ?? B.
Proof.
  intros. unfold not. intros.
  assert (x ?? (App A B)). { constructor. auto. } auto.
Qed.

Lemma FV_Lam_body : forall A x y, x <> y -> not x ?? (Lam y A) -> not x ?? A.
Proof.
  intros. unfold not. intros.
  assert (x ?? (Lam y A)). { constructor. auto. auto. } auto.
Qed.