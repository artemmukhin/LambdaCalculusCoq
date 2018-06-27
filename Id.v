(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof.
  intros.
  destruct id1, id2.
  (* or intros [n] [m] *)

  remember (lt_eq_lt_dec n n0).
  destruct s. destruct s.
  - left. left. constructor. assumption.
  - left. right. rewrite e. reflexivity.
  - right. constructor. assumption.
Qed.

(**  SearchAbout nat. *)

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof.
  intros.
  destruct id1, id2.
  remember (lt_eq_lt_dec n n0).
  destruct s. destruct s.
  - right. constructor. assumption.
  - left. right. rewrite e. reflexivity.
  - left. left. constructor. assumption.
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof.
  intros.
  destruct id1, id2.
  remember (le_gt_dec n n0).
  destruct s.
  - left. constructor. assumption.
  - right. constructor. assumption.
Qed.


Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n. intros.
  - destruct m as [|m]. auto. auto.
  - destruct m as [|m]. auto.
    destruct (IHn m). auto. auto.
Qed.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros.
  destruct id1, id2.
  remember (eq_dec n n0).
  destruct s.
  - auto.
  - right. unfold not in *. intro. inversion H. contradiction.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p. 
Proof.
  intros.
  destruct (eq_id_dec x x); tauto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof.
  intros.
  destruct (eq_id_dec x y); tauto.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof.
  intros.
  destruct id1, id2.
  inversion_clear H.
  inversion_clear H0.
  omega.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof.
  intros.
  destruct id1, id2.
  inversion_clear H.
  inversion_clear H0.
  omega.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof.
  intros.
  destruct id1, id2.
  remember (le_lt_eq_dec n n0).
  destruct s.
  - inversion_clear H. auto.
  - right. constructor. auto.
  - left. rewrite e. auto.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof.
  intros.
  remember (gt_eq_gt_id_dec id1 id2).
  destruct s. destruct s.
  auto.
  tauto.
  auto.
Qed.

  
Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof.
  intros.
  destruct id1, id2.
  inversion_clear H0.
  inversion H.
  omega.
Qed.