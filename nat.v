Inductive natural: Set :=
  | Zero: natural
  | Succ: natural -> natural.

Eval compute in (Zero).
Eval compute in (Succ(Succ(Zero))).

Fixpoint add (a b : natural) : natural :=
  match a with
  | Zero => b
  | Succ a' => Succ (add a' b)
  end.

Eval compute in (add Zero Zero).
Eval compute in (add (Succ(Zero)) Zero).
Eval compute in (add (Succ(Zero)) (Succ(Zero))).

Extraction Language Haskell.
Extraction natural.
Extraction add.

Theorem add_assoc : forall n m o,
                    add (add n m) o = add n (add m o).
Proof.
  induction n.

  intros.
  simpl.
  reflexivity.

  intros.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Print add_assoc.

Lemma add_zero : forall n,
                 add n Zero = n.
Proof.
  induction n.

  simpl.
  reflexivity.

  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Print add_zero.

Lemma add_succ : forall n m,
                 add n (Succ m) = Succ (add n m).
Proof.
  induction n.

  simpl.
  intros.
  reflexivity.

  simpl.
  intros.
  rewrite IHn.
  reflexivity.
Qed.

Theorem add_comm : forall n m,
                   add n m = add m n.
Proof.
  induction n.

  intros.
  simpl.
  rewrite add_zero.
  reflexivity.

  intros.
  simpl.
  rewrite IHn.
  rewrite add_succ.
  reflexivity.
Qed.
