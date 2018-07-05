Require Import Id.
Require Import Arith.
Require Import Term.
Require Import FreeVars.
Require Import Vars.
Require Import CAS.


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
  - subst. constructor.
    + auto.
    + assert (CAS B y x A). { apply CAS_symm. auto. auto. }
      remember (CAS_symm_var A B x y). auto.
    + apply CAS_symm. auto. auto.
Qed.

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


Lemma alpha_eq_App_rev1: forall A B C D, App A B ~a~ App C D -> A ~a~ C.
Proof.
  intros. inversion H.
  - inversion H0.
  - subst. auto.
Qed. 

Lemma alpha_eq_App_rev2: forall A B C D, App A B ~a~ App C D -> B ~a~ D.
Proof.
  intros. inversion H.
  - inversion H0.
  - subst. auto.
Qed.


Lemma alpha_eq_Lam_CAS: forall A B x y, Lam x A ~a_conv~> Lam y B -> CAS A x y B.
Proof.
  intros.
  inversion H; subst.
  - apply CAS_refl.
  - auto.
Qed.


Lemma alpha_eq_refl: forall A, A ~a~ A.
Proof.
    intros.
    induction A.
    - apply alpha_eq_Var.
    - apply alpha_eq_App. auto. auto.
    - apply alpha_eq_Lam. auto.
Qed.

Lemma alpha_eq_Lam_rev: forall A B x, Lam x A ~a~ Lam x B -> A ~a~ B.
Proof.
  intros. inversion H.
  - subst. inversion H0. subst. apply alpha_eq_refl. subst.
    exfalso. auto.
  - subst. auto.
Qed.


Lemma alpha_eq_symm: forall A B, A ~a~ B -> B ~a~ A.
Proof.
    induction A.
    - intros. inversion H.
      + exfalso. inversion H0.
      + subst. auto.
    - intros. inversion H.
      + exfalso. inversion H0.
      + subst.
        assert (B0 ~a~ A1). { apply IHA1. auto. }
        assert (D ~a~ A2). { apply IHA2. auto. }
        apply alpha_eq_App.
        auto. auto.
    - intros. inversion H.
      + subst. inversion H0.
        * subst. auto.
        * subst. constructor.
          constructor.
          ** auto.
          ** remember (CAS_symm_var A A' i y). auto.
          ** apply CAS_symm. auto. auto.
      + subst. assert (B0 ~a~ A). auto. apply alpha_eq_Lam. auto.
Qed.

Lemma alpha_eq_trans: forall C A B, A ~a~ B -> B ~a~ C -> A ~a~ C.
Proof.
  intros C.
  induction C.
  - intros. inversion H.
    + subst. inversion H1.
      * subst. auto.
      * subst. exfalso. inversion H0. inversion H5.
    + subst. auto.
    + subst. exfalso. inversion H0. inversion H2.
    + subst. exfalso. inversion H0. inversion H3. 

  - intros. inversion H.
    + subst. inversion H0.
      * subst. inversion H2.
      * subst. inversion H1.
    + subst. exfalso. inversion H0. inversion H1.
    + subst. exfalso. inversion H0. inversion H2.
    + subst.
      assert (B0 ~a~ C1). { apply alpha_eq_App_rev1 in H0. auto. }
      assert (D ~a~ C2). { apply alpha_eq_App_rev2 in H0. auto. }
      assert (A0 ~a~ C1). { specialize (IHC1 A0 B0). auto. }
      assert (C ~a~ C2). { specialize (IHC2 C D). auto. }
      apply alpha_eq_App. auto. auto.
      
  - intros. inversion H.
    + subst. inversion H1.
      * subst. auto. 
      * subst.
        destruct (eq_id_dec i x).
        **  subst. apply alpha_eq_Lam.
            inversion H0.
            --  subst. inversion H5. subst. exfalso. auto.
                subst. apply CAS_symm in H4.
                assert (A0 = C).
                remember (CAS_deterministic A' A0 C y x).
                auto. subst. apply alpha_eq_refl. auto.
            --  subst. exfalso. auto.
        **  constructor. constructor.
            --  auto.
            --  inversion H0. inversion H5.
                --- subst. auto.
                --- subst.
                    remember (CAS_subst_other A0 A' x y i).
                    auto.
                --- subst. auto.
            --  destruct (eq_id_dec i y).
                ++  subst. admit.
                ++  assert (CAS A' y i C). {
                    inversion H0.
                    - subst. apply alpha_eq_Lam_CAS. auto.
                    - subst. exfalso. auto.
                  }
                  apply (CAS_comp A0 A' C x y i).
                  auto. auto.

    + subst. exfalso. inversion H0. inversion H1.
    
    + subst. destruct (eq_id_dec i x).
      * subst. apply alpha_eq_Lam.
        assert (B0 ~a~ C). { apply alpha_eq_Lam_rev in H0. auto. }
        specialize (IHC A0 B0). auto.
      * constructor. constructor.
        -- auto.
        -- admit.
        -- inversion H0.
          ++  subst. inversion H2.
              +++ subst. exfalso. auto.
              +++ subst. inversion H1. admit.
          ++  subst. exfalso. auto.

    + subst. exfalso. inversion H0. inversion H3.
Admitted.