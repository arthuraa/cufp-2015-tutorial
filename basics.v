(* ###################################################################### *)
(** * Proofs and Programs *)

(** Everything in Coq is built from scratch -- even booleans!
    Fortunately, they are already provided by the Coq standard
    library, but we'll review their definition here to get familiar
    with the basic features of the system.

    [Inductive] is Coq's way of defining an algebraic datatype.  Its
    syntax is similar to OCaml's ([type]) or Haskell's ([data]). Here,
    we define [bool] as a simple algebraic datatype. *)

Module Bool.

Inductive bool : Type :=
| true : bool
| false : bool.

(** Exercise: Define a three-valued data type, representing ternary
    logic.  Here something can be true, false and unknown. *)

(* 30 seconds *)
Inductive trivalue : Type :=
  (* Fill in here *).

(** We can write functions that operate on [bool]s by simple pattern
    matching, using the [match] keyword. *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(** We can pattern-match on multiple arguments simultaneously, and
    also use "_" as a wildcard pattern. *)

Definition orb (b1 b2: bool) : bool :=
  match b1, b2 with
  | false, false => false
  | _, _ => true
  end.

Print orb.

(** We can also use an If statement, which matches on the first constructor of
    any two-constructor datatype, in our definition. *)

Definition andb (b1 b2: bool) : bool := if b1 then b2 else false.

(** Let's test our functions. The [Compute] command tells Coq to
    evaluate an expression and print the result on the screen.*)

Compute (negb true).
Compute (orb true false).
Compute (andb true false).

(** Exercise: Define xor (exclusive or) . *)

(* 30 seconds *)
Definition xorb (b1 b2 : bool) : bool :=
  true (* Change this! *).


Compute (xorb true true).


(** What makes Coq different from normal functional programming
    languages is that it allows us to formally _prove_ that our
    programs satisfy certain properties. The system mechanically
    verifies these proofs to ensure that they are correct.

    We use [Lemma], [Theorem] and [Example] to write logical
    statements. Coq requires us to prove these statements using
    _tactics_, which are commands that manipulate formulas using basic
    logic rules. Here's an example showing some basic tactics in
    action.


    New tactics
    -----------

    - [intros]: Introduce variables into the context, giving them
      names.

    - [simpl]: Simplify the goal.

    - [reflexivity]: Prove that some expression [x] is equal to itself. *)

Example andb_false_l : forall b, andb false b = false.
Proof.
  intros b. (* introduce the variable b *)
  simpl. (* simplify the expression *)
  reflexivity. (* solve for x = x *)
Qed.

(* 30 seconds *)
(** Exercise: Prove this. *)
Theorem orb_true_l :
  forall b, orb true b = true.
Proof. (* Fill in here *) Admitted.

(** Some proofs require case analysis. In Coq, this is done with the
    [destruct] tactic.


    New tactics
    -----------

    - [destruct]: Consider all possible constructors of an inductive
      data type, generating subgoals that need to be solved
      separately.


    Here's an example of [destruct] in action. *)

Lemma orb_true_r : forall b : bool, orb b true = true.
(* Here we explicitly annotate b with its type, even though Coq could infer it. *)
Proof.
  intros b.
  simpl. (* This doesn't do anything, since orb pattern matches on the
  first variable first. *)
  destruct b. (* Do case analysis on b *)
  + (* We use the "bullets" '+' '-' and '*' to delimit subgoals *)
    (* true case *)
    simpl.
    reflexivity.
  + (* false case *)
    simpl.
    reflexivity.
Qed.

(** We can call [destruct] as many times as we want, generating deeper subgoals. *)

Theorem andb_commutative : forall b1 b2 : bool, andb b1 b2 = andb b2 b1.
Proof.
  intros b1 b2.
  destruct b1.
  + destruct b2.
    - simpl. reflexivity.
    - simpl. reflexivity. (* bullets need to be consistent *)

(** Alternatively, if all the subgoals are solved the same way, we can
    use the [;] operator to execute a tactic on _all_ the generated
    subgoals, like this: *)

  + destruct b2; simpl; reflexivity.
Qed.

(** Exercise: Show that false is an identity element for xor -- that
    is, [xor false b] is equal to [b] *)


(* 1 minute *)
(* Exercise: Show that b AND false is always false  *)
Theorem andb_false_r : False. (* Replace [False] with claim. *)
Proof.
Admitted.

(* Exercise: Show that b xor (not b) is always true. *)
Theorem xorb_b_neg_b : False. (* Replace [False] with claim. *)
Proof.
Admitted. (* fill in proof *)

(** NB: Admitted allows us to proceed without completing our proof.

    Sometimes, we want to show a result that requires hypotheses. In
    Coq, [P -> Q] means that [P] implies [Q], or that [Q] is true
    whenever [P] is. We can use [->] multiple times to express that
    more than one hypothesis are needed; the syntax is similar to how
    we write multiple-argument functions in OCaml or Haskell. For
    example: *)

Theorem rewrite_example : forall b1 b2 b3 b4,
  b1 = b4 ->
  b2 = b3 ->
  andb b1 b2 = andb b3 b4.

(** We can use the [intros] tactic to give hypotheses names, bringing
    them into the proof context. *)

Proof.
  intros b1 b2 b3 b4 eq14 eq23.

(** Now, our context has two hypotheses: [eq14], which states that [b1
    = b4], and [eq23], stating that [b2 = b3].

    Here are some tactics for using hypotheses and previously proved
    results:


    New tactics
    -----------

    - [rewrite]: Replace one side of an equation by the other.

    - [apply]: Suppose that the current goal is [Q]. If [H : Q], then
      [apply H] solves the goal. If [H : P -> Q], then [apply H]
      replaces [Q] by [P] in the goal. If [H] has multiple hypotheses,
      [H : P1 -> P2 -> ... -> Pn -> Q], then [apply H] generates one
      subgoal for each [Pi]. *)

  rewrite eq14. (* replace b1 with b4 in the goal *)
  rewrite <- eq23. (* replace b3 with b2 in the goal. *)
  apply andb_commutative. (* solve using our earlier theorem *)
Qed.


(* 30 seconds *)
(** Exercise: Show that if [b1 = b2] then [xorb b1 b2] is equal to
    [false] *)

Theorem xorb_same : False. (* Replace [False] by claim *)
Proof.
  Admitted. (* fill in proof *)

End Bool.

Module Nat.

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

    In this case, we can rewrite [div] so that it is accepted by Coq's
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
