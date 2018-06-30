Require Import Term.
Require Import Id.
Require Import FreeVars.


(* Capture-avoiding substitution *)
Inductive CAS : term -> id -> id -> term -> Prop :=
  | CAS_Var1 : forall x y, CAS (Var x) x y (Var y)
  | CAS_Var2 : forall x y z, z <> x -> CAS (Var z) x y (Var z)
  | CAS_App  : forall A B A' B' x y, CAS A x y A' -> CAS B x y B' -> CAS (App A B) x y (App A' B')
  | CAS_Lam1 : forall A x y, CAS (Lam x A) x y (Lam x A)
  | CAS_Lam2 : forall A A' x y z, z <> x -> z <> y -> CAS A x y A' -> CAS (Lam z A) x y (Lam z A')
  | CAS_Lam3 : forall A A' A'' x y z, not z ?? A -> CAS A y z A'' -> CAS A'' x y A' -> CAS (Lam y A) x y (Lam z A')
.
