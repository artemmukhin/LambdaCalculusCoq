Require Import Id.

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

Lemma induction_by_height : 
   forall P : term -> Prop, 
   (forall t, height t = 0 => P t) -> 
   (forall n t, height t = n -> P t => (forall t', height t' = n+1 -> P t')) ->
   (forall t, P t).

