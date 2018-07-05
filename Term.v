Require Import Id.
Require Import Arith Arith.EqNat.
Require Import Omega.

(* Lambda term definition *)
Inductive term : Type :=
    | Var : id -> term
    | App : term -> term -> term
    | Lam : id -> term -> term.

Hint Constructors term.

Definition x := (Id 1).
Definition y := (Id 2).
Definition z := (Id 3).

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Fixpoint height t :=
  match t with
  | Var _   => 0
  | App m n => 1 + max (height m) (height n)
  | Lam _ m => 1 + height m
  end.


Lemma max_lemma : forall x y z, max x y = z -> z = x \/ z = y.
Proof.
  intros. destruct (Max.max_dec x0 y0); subst; auto.
Qed. 

Lemma induction_by_height :
  forall (P : term -> Prop), 
  (forall t, height t = 0 -> P t) -> 
  (forall n t, height t = n -> P t -> (forall t', height t' = n+1 -> P t')) ->
  (forall t, P t).
Proof.
  intros.
  induction t.
  - auto.
  - destruct (max_lemma (height t1) (height t2) (height (App t1 t2) - 1)).
    + simpl. omega.
    + specialize (H0 (height t1) t1).
      assert (height (App t1 t2) = height t1 + 1). { rewrite <- H1. simpl. omega. }
      clear H1.
      assert (forall t' : term, height t' = height t1 + 1 -> P t') by auto.
      specialize (H1 (App t1 t2)). auto.
    + specialize (H0 (height t2) t2).
      assert (height (App t1 t2) = height t2 + 1). { rewrite <- H1. simpl. omega. }
      clear H1.
      assert (forall t' : term, height t' = height t2 + 1 -> P t') by auto.
      specialize (H1 (App t1 t2)). auto.
  
  - specialize (H0 (height t) t).
    assert (height (Lam i t) = height t + 1). { simpl. omega. }
    assert (forall t' : term, height t' = height t + 1 -> P t') by auto.
    specialize (H2 (Lam i t)). auto.
Qed.
