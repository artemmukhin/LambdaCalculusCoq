Require Import Term.
Require Import Id.
Require Import Vars.


(* Simple (not capture-avoiding) substitution *)
Reserved Notation "'[' x ':=' s ']' A" (at level 20).
Fixpoint subst (x y : id) (A : term) : term :=
  match A with
  | Var x' => if eq_id_dec x x' then (Var y) else (Var x')

  | Lam x' A1 =>
      Lam x' (if eq_id_dec x x' then A1 else ([x:=y] A1))

  | App A1 A2 =>
      App ([x:=y] A1) ([x:=y] A2)
  end
where "'[' x ':=' y ']' A" := (subst x y A).


Lemma subst_same : forall x A, ([x := x] A) = A.
Proof.
    intros.
    induction A.
    - simpl. destruct (eq_id_dec x i).
      + subst. auto.
      + auto.
    - simpl. rewrite -> IHA1. rewrite -> IHA2. auto.
    - destruct (eq_id_dec x i).
      + subst. simpl. destruct (eq_id_dec i i).
        ++ auto.
        ++ exfalso. auto.
      + simpl. destruct (eq_id_dec x i).
        ++ exfalso. auto.
        ++ rewrite -> IHA. auto.
Qed. 

Lemma subst_other : forall x y A, not x ? A -> [x:=y] A = A.
Proof.
  intros.
  induction A.
  - remember (V_Var_other2 x i). assert (x <> i) by auto.
    simpl. apply neq_id. auto.
  
  - simpl.
    remember (V_App_not1 x A1 A2).
    assert (not (x) ? (A1)) by auto.
    remember (V_App_not2 x A1 A2).
    assert (not (x) ? (A2)) by auto.

    assert ([x := y] A1 = A1) by auto.
    assert ([x := y] A2 = A2) by auto.

    rewrite -> H2. rewrite -> H3. auto.

  - remember (V_Lam_var i x A).
    assert (x <> i) by auto.
    simpl.
    destruct eq_id_dec.
    + exfalso. auto.
    + remember (V_Lam_body i x A).
    assert (not x ? A) by auto.
    assert ([x := y] A = A) by auto.
    rewrite -> H2. auto.
Qed.

Lemma subst_var : forall x y, ([x := y] Var x) = Var y.
Proof.
    intros.
    destruct (eq_id_dec x y).
    - subst. apply subst_same.
    - simpl. apply eq_id.
Qed.

Lemma subst_rev : forall x y A, not y ? A -> [y:=x] ([x:=y] A) = A.
Proof.
  intros.
  induction A.
  - simpl. destruct eq_id_dec.
    + subst. simpl. apply eq_id.
    + simpl. destruct eq_id_dec.
      * subst. clear n. exfalso.
        assert (i ? (Var i)) by constructor. auto.
      * auto.

  - simpl.
    assert (not y ? A1). {
      apply (V_App_not1 y A1 A2). auto.
    }
    assert (not y ? A2). {
      apply (V_App_not2 y A1 A2). auto.
    }
    assert ([y := x] ([x := y] A1) = A1) by auto.
    assert ([y := x] ([x := y] A2) = A2) by auto.
    rewrite -> H2. rewrite -> H3. auto.

  - simpl. destruct eq_id_dec.
    + subst. exfalso. clear IHA.
      assert (i ? (Lam i A)). { constructor. auto. }
      auto.
    + destruct eq_id_dec.
      * subst. remember (subst_other y i A).
        remember (V_Lam_body i y A).
        assert (not y ? A) by auto.
        assert ([y := i] A = A) by auto.
        rewrite -> H1. auto.
      * remember (V_Lam_body i y A).
        assert (not y ? A) by auto.
        assert ([y := x] ([x := y] A) = A) by auto.
        rewrite -> H1. auto.
Qed.

Lemma subst_comp : forall x y z A, not y ? A -> not z ? A -> [y:=z] ([x:=y] A) = [x:=z] A.
Proof.
  intros.
  induction A.
  - simpl. destruct eq_id_dec.
    + subst. simpl. apply eq_id.
    + simpl. destruct eq_id_dec.
      * subst. clear n. exfalso.
        assert (i ? (Var i)) by constructor. intuition.
      * auto.
  
  - simpl.
  assert (not y ? A1). { apply (V_App_not1 y A1 A2). intuition. }
  assert (not y ? A2). { apply (V_App_not2 y A1 A2). intuition. }

  assert (not z ? A1). { apply (V_App_not1 z A1 A2). intuition. }
  assert (not z ? A2). { apply (V_App_not2 z A1 A2). intuition. }

  assert ([y := z] ([x := y] A1) = [x := z] A1). { intuition. }
  assert ([y := z] ([x := y] A2) = [x := z] A2). { intuition. }
  rewrite -> H5. rewrite -> H6. auto.

  - simpl. destruct eq_id_dec.
  + subst. exfalso. clear IHA.
    assert (i ? (Lam i A)). { constructor. auto. }
    intuition.
  + destruct eq_id_dec.
    * subst. remember (subst_other y i A). clear Heqe.
      remember (V_Lam_body i y A). clear Heqn0.
      assert (not y ? A) by intuition.
      remember (V_Lam_body i z A). clear Heqn1.
      assert (not z ? A) by intuition.
      remember (subst_other y z A).
      assert ([y := z] A = A) by intuition.
      rewrite -> H3. auto.
    * assert (not y ? A). { apply (V_Lam_body i y A). intuition. }
      assert (not z ? A). { apply (V_Lam_body i z A). intuition. }
      assert ([y := z] ([x := y] A) = [x:=z] A) by auto.
      rewrite -> H3. auto.
Qed.
