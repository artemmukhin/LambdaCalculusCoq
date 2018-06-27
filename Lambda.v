Require Import Arith.
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


(* Free variables of a term *)
Reserved Notation "x ?? e" (at level 0).
Inductive FV : term -> id -> Prop := 
    | FV_Var : forall (x : id), x ?? (Var x)
    | FV_App : forall (x : id) (t1 t2 : term), x ?? t1 \/ x ?? t2 -> x ?? (App t1 t2)
    | FV_Lam : forall (x y : id) (t : term), y ?? t /\ x <> y -> y ?? (Lam x t)
where "x ?? e" := (FV e x).

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
  assert (y0 ? (Var y0)) by constructor.
  auto.
Qed.

Lemma V_App_not1 : forall x A B, not x ? (App A B) -> not x ? A.
Proof.
  intros. unfold not. intros.
  assert (x0 ? (App A B)). { constructor. auto. } auto.
Qed.

Lemma V_App_not2 : forall x A B, not x ? (App A B) -> not x ? B.
Proof.
  intros. unfold not. intros.
  assert (x0 ? (App A B)). { constructor. auto. } auto.
Qed.

Lemma V_Lam_var : forall x y A, not y ? (Lam x A) -> y <> x.
Proof.
  intros. unfold not. intros.
  rewrite H0 in H.
  assert (x0 ? (Lam x0 A)). { constructor. auto. } auto.
Qed.

Lemma V_Lam_body : forall x y A, not y ? (Lam x A) -> not y ? A.
Proof.
  intros. unfold not. intros.
  assert (y0 ? (Lam x0 A)). { constructor. auto. } auto.
Qed.

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
    - simpl. destruct (eq_id_dec x0 i).
      + subst. auto.
      + auto.
    - simpl. rewrite -> IHA1. rewrite -> IHA2. auto.
    - destruct (eq_id_dec x0 i).
      + subst. simpl. destruct (eq_id_dec i i).
        ++ auto.
        ++ exfalso. auto.
      + simpl. destruct (eq_id_dec x0 i).
        ++ exfalso. auto.
        ++ rewrite -> IHA. auto.
Qed. 

Lemma subst_other : forall x y A, not x ? A -> [x:=y] A = A.
Proof.
  intros.
  induction A.
  - remember (V_Var_other2 x0 i). assert (x0 <> i) by auto.
    simpl. apply neq_id. auto.
  
  - simpl.
    remember (V_App_not1 x0 A1 A2).
    assert (not (x0) ? (A1)) by auto.
    remember (V_App_not2 x0 A1 A2).
    assert (not (x0) ? (A2)) by auto.

    assert ([x0 := y0] A1 = A1) by auto.
    assert ([x0 := y0] A2 = A2) by auto.

    rewrite -> H2. rewrite -> H3. auto.

  - remember (V_Lam_var i x0 A).
    assert (x0 <> i) by auto.
    simpl.
    destruct eq_id_dec.
    + exfalso. auto.
    + remember (V_Lam_body i x0 A).
    assert (not x0 ? A) by auto.
    assert ([x0 := y0] A = A) by auto.
    rewrite -> H2. auto.
Qed.

Lemma subst_var : forall x y, ([x := y] Var x) = Var y.
Proof.
    intros.
    destruct (eq_id_dec x0 y0).
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
    assert (not y0 ? A1). {
      apply (V_App_not1 y0 A1 A2). auto.
    }
    assert (not y0 ? A2). {
      apply (V_App_not2 y0 A1 A2). auto.
    }
    assert ([y0 := x0] ([x0 := y0] A1) = A1) by auto.
    assert ([y0 := x0] ([x0 := y0] A2) = A2) by auto.
    rewrite -> H2. rewrite -> H3. auto.

  - simpl. destruct eq_id_dec.
    + subst. exfalso. clear IHA.
      assert (i ? (Lam i A)). { constructor. auto. }
      auto.
    + destruct eq_id_dec.
      * subst. remember (subst_other y0 i A).
        remember (V_Lam_body i y0 A).
        assert (not y0 ? A) by auto.
        assert ([y0 := i] A = A) by auto.
        rewrite -> H1. auto.
      * remember (V_Lam_body i y0 A).
        assert (not y0 ? A) by auto.
        assert ([y0 := x0] ([x0 := y0] A) = A) by auto.
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
  assert (not y0 ? A1). { apply (V_App_not1 y0 A1 A2). intuition. }
  assert (not y0 ? A2). { apply (V_App_not2 y0 A1 A2). intuition. }

  assert (not z0 ? A1). { apply (V_App_not1 z0 A1 A2). intuition. }
  assert (not z0 ? A2). { apply (V_App_not2 z0 A1 A2). intuition. }

  assert ([y0 := z0] ([x0 := y0] A1) = [x0 := z0] A1). { intuition. }
  assert ([y0 := z0] ([x0 := y0] A2) = [x0 := z0] A2). { intuition. }
  rewrite -> H5. rewrite -> H6. auto.

  - simpl. destruct eq_id_dec.
  + subst. exfalso. clear IHA.
    assert (i ? (Lam i A)). { constructor. auto. }
    intuition.
  + destruct eq_id_dec.
    * subst. remember (subst_other y0 i A). clear Heqe.
      remember (V_Lam_body i y0 A). clear Heqn0.
      assert (not y0 ? A) by intuition.
      remember (V_Lam_body i z0 A). clear Heqn1.
      assert (not z0 ? A) by intuition.
      remember (subst_other y0 z0 A).
      assert ([y0 := z0] A = A) by intuition.
      rewrite -> H3. auto.
    * assert (not y0 ? A). { apply (V_Lam_body i y0 A). intuition. }
      assert (not z0 ? A). { apply (V_Lam_body i z0 A). intuition. }
      assert ([y0 := z0] ([x0 := y0] A) = [x0:=z0] A) by auto.
      rewrite -> H3. auto.
Qed.

(* Capture-avoiding substitution *)
Inductive CAS : term -> id -> id -> term -> Prop :=
  | CAS_Var1 : forall x y, CAS (Var x) x y (Var y)
  | CAS_Var2 : forall x y z, z <> x -> CAS (Var z) x y (Var z)
  | CAS_App  : forall A B A' B' x y, CAS A x y A' -> CAS B x y B' -> CAS (App A B) x y (App A' B')
  | CAS_Lam1 : forall A x y, CAS (Lam x A) x y (Lam x A)
  | CAS_Lam2 : forall A A' x y z, z <> x -> z <> y -> CAS A x y A' -> CAS (Lam z A) x y (Lam z A')
  | CAS_Lam3 : forall A A' A'' x y z, not z ?? A -> CAS A y z A'' -> CAS A'' x y A' -> CAS (Lam y A) x y (Lam z A')
.


(* Alpha-conversion *)
Reserved Notation "t1 '~a_conv~>' t2" (at level 42, no associativity).
Inductive alpha_conv : term -> term -> Prop :=
    | alpha_conv_Lam1 : forall x A,
        Lam x A ~a_conv~> Lam x A
    | alpha_conv_Lam2 : forall x y A A',
        x <> y -> not y ?? A -> CAS A x y A' -> Lam x A ~a_conv~> Lam y A'
where "t1 '~a_conv~>' t2" := (alpha_conv t1 t2).

Lemma alpha_conv_refl : forall x A, Lam x A ~a_conv~> Lam x A.
Proof.
  intros.
  constructor.
Qed.

Lemma alpha_conv_symm : forall A B x y, Lam x A ~a_conv~> Lam y B -> Lam y B ~a_conv~> Lam x A.
Proof.
  intros.
  inversion H.
  - subst. auto.
  - subst. constructor. admit.
Admitted.

Lemma alpha_conv_trans : forall A B C x y z, Lam x A ~a_conv~> Lam y B -> Lam y B ~a_conv~> Lam z C -> Lam x A ~a_conv~> Lam z C.
Proof.
  admit.
Admitted.


(* Alpha-equivalence *)
Reserved Notation "t1 '~a~' t2" (at level 42, no associativity).
Inductive alpha_eq : term -> term -> Prop :=
    | alpha_eq_conv : forall A B,
        A ~a_conv~> B -> A ~a~ B

    | alpha_eq_Var : forall x,
        Var x ~a~ Var x

    | alpha_eq_Lam : forall x A B,
        A ~a~ B -> Lam x A ~a~ Lam x B

    | alpha_eq_App : forall A B C D,
        A ~a~ B -> C ~a~ D -> App A C ~a~ App B D
where "t1 '~a~' t2" := (alpha_eq t1 t2).


Lemma alpha_eq_refl: forall (A : term), A ~a~ A.
Proof.
    intros.
    induction A.
    - apply alpha_eq_Var.
    - apply alpha_eq_App. auto. auto.
    - apply alpha_eq_Lam. auto.
Qed.
