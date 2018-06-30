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
      inversion H0.
      ++ subst. apply FV_Var_other1. auto.
      ++ subst. assert (x <> z). {
          inversion H6. subst.
          - exfalso. auto.
          - subst. auto.
         }
         apply FV_Var_other1. auto.
      ++ subst. admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
    + apply CAS_symm. auto. auto.
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


Lemma alpha_eq_refl: forall A, A ~a~ A.
Proof.
    intros.
    induction A.
    - apply alpha_eq_Var.
    - apply alpha_eq_App. auto. auto.
    - apply alpha_eq_Lam. auto.
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
        * subst. admit.
      + subst. admit.
Admitted.