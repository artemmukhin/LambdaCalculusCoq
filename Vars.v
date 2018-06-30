Require Import Term.
Require Import Id.


(* All (free and closed) variables of a term *)
Reserved Notation "x ? e" (at level 0).
Inductive V : term -> id -> Prop := 
    | V_Var : forall (x : id), x ? (Var x)
    | V_App : forall (x : id) (t1 t2 : term), x ? t1 \/ x ? t2 -> x ? (App t1 t2)
    | V_Lam : forall (x y : id) (t : term), y ? t \/ x = y -> y ? (Lam x t)
where "x ? e" := (V e x).


Lemma V_Var_other1 : forall x y, x <> y -> not x ? (Var y).
Proof.
  intros.
  unfold not. intros.
  inversion H0. auto.
Qed.

Lemma V_Var_other2 : forall x y, not x ? (Var y) -> x <> y.
Proof.
  intros.
  unfold not. intros. subst.
  assert (y ? (Var y)) by constructor.
  auto.
Qed.

Lemma V_App_not1 : forall x A B, not x ? (App A B) -> not x ? A.
Proof.
  intros. unfold not. intros.
  assert (x ? (App A B)). { constructor. auto. } auto.
Qed.

Lemma V_App_not2 : forall x A B, not x ? (App A B) -> not x ? B.
Proof.
  intros. unfold not. intros.
  assert (x ? (App A B)). { constructor. auto. } auto.
Qed.

Lemma V_Lam_var : forall x y A, not y ? (Lam x A) -> y <> x.
Proof.
  intros. unfold not. intros.
  rewrite H0 in H.
  assert (x ? (Lam x A)). { constructor. auto. } auto.
Qed.

Lemma V_Lam_body : forall x y A, not y ? (Lam x A) -> not y ? A.
Proof.
  intros. unfold not. intros.
  assert (y ? (Lam x A)). { constructor. auto. } auto.
Qed.
