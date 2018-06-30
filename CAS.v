Require Import Term.
Require Import Id.
Require Import FreeVars.


(* Capture-avoiding substitution *)
Inductive CAS : term -> id -> id -> term -> Prop :=
  | CAS_Var1 : forall x y, CAS (Var x) x y (Var y)
  | CAS_Var2 : forall x y z, z <> x -> CAS (Var z) x y (Var z)
  | CAS_App  : forall A B A' B' x y, CAS A x y A' -> CAS B x y B' -> CAS (App A B) x y (App A' B')
  | CAS_Lam1 : forall A x y, CAS (Lam x A) x y (Lam x A)
  | CAS_Lam2 : forall A x y z, not x ?? A -> CAS (Lam z A) x y (Lam z A)
  | CAS_Lam3 : forall A A' x y z, z <> x -> z <> y -> CAS A x y A' -> CAS (Lam z A) x y (Lam z A')
  | CAS_Lam4 : forall A A' A'' x y z, not z ?? A -> CAS A y z A'' -> CAS A'' x y A' -> CAS (Lam y A) x y (Lam z A')
.

Hint Constructors CAS.

Lemma CAS_same: forall A B x, CAS A x x B -> A = B.
Proof.
  intros.
  admit.
Admitted.

Lemma CAS_other: forall A x y, not x ?? A -> not y ?? A -> CAS A x y A.
Proof.
  intros.
  induction A.
  - apply CAS_Var2.
    apply FV_Var_other2 in H. auto.
  - assert (not x ?? A1). { apply FV_App_not1 in H. auto. }
    assert (not x ?? A2). { apply FV_App_not2 in H. auto. }
    assert (not y ?? A1). { apply FV_App_not1 in H0. auto. }
    assert (not y ?? A2). { apply FV_App_not2 in H0. auto. }
    auto.
  - destruct (eq_id_dec x i).
    + subst. auto.
    + destruct (eq_id_dec y i). subst.
      * remember (CAS_Lam2 A x i i).
        assert (not x ?? A). { remember (FV_Lam_body A x i). auto. }
        auto.
      * remember (CAS_Lam2 A x y i).
        assert (not x ?? A). { remember (FV_Lam_body A x i). auto. }
        auto.
Qed.


Lemma CAS_symm: forall A B x y, not y ?? A -> CAS A x y B -> CAS B y x A.
Proof.
    intros.
    destruct (eq_id_dec x y).
    subst. assert (A = B). { remember (CAS_same A B y). auto. }
    subst. auto.
    
    induction A.
    - inversion H0. subst.
      + auto.
      + subst. apply CAS_other.
        destruct (eq_id_dec y i).
        * subst. exfalso. apply FV_Var_other2 in H. auto.
        * auto.
        * apply FV_Var_other1. auto.
    
    - assert (not y ?? A1). { apply FV_App_not1 in H. auto. }
      assert (not y ?? A2). { apply FV_App_not2 in H. auto. }
      inversion H0.
      subst.
      admit.
    - admit.
Admitted.

Lemma CAS_symm_var : forall A B x y, not y ?? A -> CAS A x y B -> not x ?? B.
Proof.
  intros.
  admit.
Admitted.