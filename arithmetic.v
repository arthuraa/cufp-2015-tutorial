(* ###################################################################### *)
(** * Numbers and Induction

    Even numbers are not primitive! Luckily, inductive types are all
    we need to define them. Once again, Coq's standard library comes
    with its own numeric types, but we repeat the definition of
    natural number here for illustration purposes.

    Recall that a natural number is either zero or the successor of a
    natural number. This leads to the following definition: *)

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

(** Note that [bool] was a simple enumeration type with finitely many
    elements, whereas this type has a recursive structure. This
    definition says that [nat] is an algebraic data type with two
    constructors, [O] and [S], the second of which has one argument of
    type [nat].

    We can use [Check] ([C-c C-a C-c] in Proof General) to ask Coq for
    the type of an expression. *)

Check (S (S O)).

(** This expression represents the successor of the successor of zero (i.e., two).

    We can define recursive functions with the [Fixpoint] keyword,
    which corresponds to [let rec] declarations in OCaml. (Other
    languages, such as Haskell, do not require special keywords to
    introduce recursive definitions.) Here's how we can define
    addition and multiplication for [nat]s. *)

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

(** Coq comes with a syntax extension mechanism for defining custom
    notations. Without getting into details, here's how we can give
    familiar syntax for the two functions above. *)

Notation "x + y" := (plus x y) (at level 50, left associativity).

Notation "x * y" := (mult x y) (at level 40, left associativity).


(* 90 seconds *)
(** Exercise: Define exponentiation *)

(* Fill in function here *)

(* Fill in notation here *)

(** It is easy to show that [O] is the left additive identity, because
    it follows directly from simplification: *)

Lemma plus_0_l: forall n : nat, O + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(** Showing that [O] is the right additive identity is more difficult,
    since it doesn't follow by simplification alone. *)

Lemma plus_O_r: forall n : nat, n + O = n.
Proof.
  intros n.
  simpl. (* Does nothing *)
  destruct n as [| n']. (* Notice the [as] clause, which allows us
                           to name constructor arguments. *)
  + simpl.
    reflexivity.
  + simpl. (* no way to proceed... *)

(** The problem is that we can only prove the result for [S n'] if we
    already know that it is valid for [n']. We need a bigger hammer here...


    New tactic
    ----------

    - [induction]: Argue by induction. It works as [destruct], but
    additionally giving us an inductive hypothesis in the inductive
    case. *)

Restart.
  intros n.
  induction n as [| n' IH]. (* Note the additional name [IH], given to our
                               inductive hypothesis *)
  + simpl.
    reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
Qed.

(** As a rule of thumb, when proving some property of a recursive
    function, it is a good idea to do induction on the recursive
    argument of the function. For instance, let's show that [plus] is
    associative: *)

Theorem plus_assoc: forall m n o, m + (n + o) = (m + n) + o.
Proof.
  intros m n o.
  induction m as [| m' IH]. (* m is the right choice here, since [plus] is defined
                               by recursion on the first argument. *)
  + simpl.
    reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
Qed.

(** Take-home exericse: Try to do induction on [n] and [o] in the
    above proof, and see where it fails. *)

(* 3 minutes *)
(** Exercise: Show that [n + S m] is equal to [S (n + m)]. *)

(** Exercise: Show that plus is commutative. *)
(** Hint: Look at our earlier lemmas. *)

(** Additional take-home exercises: Show that mult has an identity [S
    O], a annihilator [O] and associative, commutative and
    distributive properties. *)


(** The next function tests whether a number [m] is equal to [n]. *)

Fixpoint beq_nat (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | S m', S n' => beq_nat m' n'
  | _, _ => false
  end.

Lemma beq_nat_refl : forall n, beq_nat n n = true.
Proof.
  intros n.
  induction n as [|n IH].
  - reflexivity.
  - simpl. apply IH.
Qed.

(** The other direction requires us to reason about _contradictory_
    hypotheses. Whenever we have a hypothesis that equates two
    expressions that start with different constructors, we can use the
    [discriminate] tactic to prune that subgoal.

    This is a particular case of what is known as _the principle of
    explosion_, which states that a contradiction implies anything.


    New Tactic
    ----------

    - [discriminate]: Looks for an equation between terms starting
      with different constructors, and solves the current goal.


    We could try to proceed like this:

*)

Lemma beq_nat_true :
  forall m n, beq_nat m n = true -> m = n.
Proof.
  intros m n.
  induction m as [|m IH].
  - destruct n as [|n].
    + reflexivity.
    + simpl. intros H. discriminate.
  - destruct n as [|n].
    + simpl. intros H. discriminate.
    + simpl. intros H.
      (* stuck... *)

(** Unfortunately, we are stuck here: our induction hypothesis talks
    about [S n], while we need it to talk about [n]! This happens
    because [n] was introduced at the beginning of our proof, which
    made our induction hypothesis too specific. We can fix this by
    avoiding introducing [n], or simply by putting it back in the goal
    before calling [induction], with the [revert] tactic.


    New Tactic
    ----------

    - [revert]: The opposite of [intros]; removes variables and
      hypotheses from the context, putting them back in the goal. *)

Restart.
  intros m n. revert n.
  induction m as [|m IH].
  - intros n. destruct n as [|n].
    + reflexivity.
    + simpl. intros H. discriminate.
  - intros n. destruct n as [|n].
    + simpl. intros H. discriminate.
    + simpl. intros H.
      rewrite (IH n). (* Note that we specify an argument to the hypothesis *)
      * reflexivity.
      * apply H.
Qed.

(* 1 minute *)
(** Exercise: Prove this statement. *)

Lemma plus_eq_0 :
  forall n m,
    n + m = O -> n = O.
Proof.
  Admitted. (* fill in proof *)



(** Coq, like many other proof assistants, requires functions to be
    _total_ and defined for all possible inputs; in particular,
    recursive functions are always required to terminate.

    Since there is no general algorithm for deciding whether a
    function is terminating or not, Coq needs to settle for an
    incomplete class of recursive functions that is easy to show
    terminating. This means that, although every recursive function
    accepted by Coq is terminating, there are many recursive functions
    that always terminate but are not accepted by Coq, because it
    isn't "smart enough" to realize that they indeed terminate.

    The criterion adopted by Coq for deciding whether to accept a
    definition or not is _structural recursion_: All recursive calls
    must be performed on _sub-terms_ of the original argument.

    Note that the definition of _sub-terms_ used in context is purely syntactic
    hence the following definition fails.

**)

Definition pred (n : nat) :=
  match n with
  | O => O
  | S n => n
  end.

Fail Fixpoint factorial (n : nat) :=
  if beq_nat n O then S O else n * factorial (pred n).

(** The [Fail] keyword instructs Coq to ignore a command when it
    fails, but to fail if the command succeeds. It is useful for
    showing certain pieces of code that are not accepted by the
    language.

    In this case, we can rewrite [factorial] so that it is accepted by Coq's
    termination checker: *)

Fixpoint factorial (n : nat) :=
  match n with
  | O => S O
  | S n => S n * factorial n
  end.

End Nat.


(** As mentioned previously, [nat] is already defined in Coq's
    standard library. Coq provides special, arabic-numeral syntax for
    [nat], which is translated in terms of the [O] and [S]
    constructors. For instance, [3] is just special syntax for [S (S
    (S O))]. Similarly: *)

Compute (S (S O)).
Compute (S (S O) + S O).
