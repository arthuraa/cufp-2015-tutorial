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

(** We can also use an If statement, which matches on the first constructor of
    any two-constructor datatype, in our definition. *)

Definition andb (b1 b2: bool) : bool := if b1 then b2 else false.

(** Let's test our functions. The [Compute] command tells Coq to
    evaluate an expression and print the result on the screen.*)

Compute (negb true).
Compute (orb true false).
Compute (andb true false).

(** Exercise: Define xor (exclusive or) . *)

Definition xorb (b1 b2 : bool) : bool :=
  true (* Change this! *).

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

Example andb_false : forall b, andb false b = false.
Proof.
  intros b. (* introduce the variable b *)
  simpl. (* simplify the expression *)
  reflexivity. (* solve for x = x *)
Qed.

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

Lemma double_negation : forall b : bool, negb (negb b) = b.
(* Here we explicitly annotate b with its type, even though Coq could infer it. *)
Proof.
  intros b.
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
  + destruct b2.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(** Exercise: Show that false is an identity element for xor -- that
    is, [xor false b] is equal to [b] *)

Theorem xorb_false : False. (* Replace [False] with claim. *)
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

(** Exercise: Show that if [b1 = b2] then [xorb b1 b2] is equal to
    [false] *)

Theorem xorb_same : False. (* Replace [False] by claim *)
Proof.
  Admitted. (* fill in proof *)

End Bool.

Module Nat.

(* ###################################################################### *)
(** * Numbers and induction

    Even numbers are not primitive! Luckily, inductive types are all
    we need to define them. Once again, Coq's standard library comes
    witg its own numeric types, but we repeat the definition of
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

(** Exercise: Show that [n + S m] is equal to [S (n + m)]. *)

(** Exercise: Show that plus is commutative. *)
(** Hint: Look at our earlier lemmas. *)

(** Additional take-home exercises: Show that mult has an identity [S
    O], a annihilator [O] and associative, commutative and
    distributive properties. *)

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
    must be performed on _sub-terms_ of the original argument. The
    definition of [plus] above is valid because the only recursive
    call to [plus] is performed on [n'], which is an argument of [S n'
    = n], hence a sub-term.

    To understand what this restriction means in practice, let's see
    how we can define a division operation in Coq. We begin by
    defining subtraction: *)

Fixpoint minus (m n : nat) : nat :=
  match m, n with
  | O, _ => m
  | _, O => m
  | S m', S n' => minus m' n'
  end.

Notation "x - y" := (minus x y) (at level 50, left associativity).

(** The next function tests whether a number [m] is less than or equal
    to [n]. *)

Fixpoint ble_nat (m n : nat) : bool :=
  match m, n with
  | O, _ => true
  | _, O => false
  | S n', S m' => ble_nat n' m'
  end.

(** We could try to define division using [minus] and [ble_nat] as in
    the definition below. Unfortunately, Coq doesn't accept this
    definition because it cannot figure out that [m - n] is smaller
    than [m] when [n] is different from [O] and [ble_nat n m = true]. *)

Fail Fixpoint div (m n: nat) : nat :=
  match n with
  | O => O
  | S n' => if ble_nat n m then S (div (m - n) n) else O
  end.

(** The [Fail] keyword instructs Coq to ignore a command when it
    fails, but to fail if the command succeeds. It is useful for
    showing certain pieces of code that are not accepted by the
    language.

    In this case, we can rewrite [div] so that it is accepted by Coq's
    termination checker: *)

Fixpoint div (m n: nat) : nat :=
  match n with
  | O => O
  | S n' => match m with
            | O => O
            | S m' => S (div (S m' - S n') (S n'))
            end
  end.

(** Here, Coq is able to figure out that [S m' - S n'] is a valid
    recursive argument because [minus] only returns results that are
    syntatic sub-terms of [m]. Unfortunately, this criterion is pretty
    fragile: replacing [m] by [O] or [S m'] in the above definition of
    [minus] causes this definition of [div] to break; try it!.

    This kind of rewriting doesn't always work, alas. We can make Coq
    accept less obvious recursive definitions by providing an
    explicit, separate proof that they always terminate, or by
    supplying an extra argument that gives an upper bound on how many
    recursive calls can be performed. We won't cover this feature in
    this tutorial, but you can find more about recursive definitions
    in Coq on the Internet. *)


(** The next function tests whether a number [m] is equal to [n]. *)

Fixpoint beq_nat (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | S m', S n' => beq_nat m' n'
  | _, _ => false
  end.

(** You may wonder why we bother defining [beq_nat] when we already
    have an equality operator [=]. This is due to an important
    distinction between propositions [Prop] and [bool] in Coq. As we
    just showed, functions in Coq are total and terminating; in
    particular, every function in Coq that returns a [bool]
    corresponds to an algorithm that returns [true] or [false] at the
    end. In contrast, we can use [Prop] to express _arbitrary_
    propositions, even ones that cannot be decided by an algorithm
    (e.g., this Turing machine halts on all inputs). Since [Prop]s do
    not correspond to terminating computations, we cannot use them to
    define functions, like this one: *)

Definition max (m n : nat) : nat :=
  if ble_nat m n then n else m.

(** Nevertheless, we can still relate our previous equality operator
    [=] to this computational notion of equality we just defined.

    New tactic
    ----------

    - [clear]: Remove hypotheses from the context (needed here to
      simplify our IH). *)

Lemma beq_nat_eq :
  forall m n, m = n -> beq_nat m n = true.
Proof.
  intros m n e. rewrite e. clear m e.
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

    New tactics
    -----------

    - [discriminate]: Looks for an equation between terms starting
      with different constructors, and solves the current goal.
*)

Lemma eq_beq_nat :
  forall m n, beq_nat m n = true -> m = n.
Proof.
  intros m.
  induction m as [|m IH].
  - intros k. destruct k as [|].
    + reflexivity.
    + simpl. intros H. discriminate.
  - intros k. destruct k as [|k].
    + simpl. intros H. discriminate.
    + simpl. intros H.
      apply IH in H.
      rewrite H.
      reflexivity.
Qed.

(** (Alternatively, we can also rewrite with [IH] while specifying
    which value of [n] to use (in this case, [k]) by writing [IH k].)
    *)

Lemma eq_beq_nat' :
  forall m n, beq_nat m n = true -> m = n.
Proof.
  intros m.
  induction m as [|m IH].
  - intros k. destruct k as [|].
    + reflexivity.
    + simpl. intros H. discriminate.
  - intros k. destruct k as [|k].
    + simpl. intros H. discriminate.
    + simpl. intros H.
      rewrite (IH k).
      * reflexivity.
      * apply H.
Qed.

(** Exercise: Prove this statement. *)

Lemma plus_eq_0 :
  forall n m,
    n + m = O -> n = O.
Proof. (* Fill in here *) Admitted.

End Nat.


(** As mentioned previously, [nat] is already defined in Coq's
    standard library. Coq provides special, arabic-numeral syntax for
    [nat], which is translated in terms of the [O] and [S]
    constructors. For instance, [3] is just special syntax for [S (S
    (S O))]. Similarly: *)

Compute (S (S O)).
Compute (S (S O) + S O).

(* ###################################################################### *)
(** * Lists

    We will now shift gears and study more interesting functional
    programs; namely, programs that manipulate _lists_. *)

Module List.

(** Here's a polymorphic definition of a [list] type in Coq: *)

Inductive list (T : Type) :=
| nil : list T
| cons : T -> list T -> list T.

(** In Coq, polymorphism is _explicit_, which means that we need to
    supply type arguments when using polymorphic functions. *)

Definition singleton_list (T : Type) (x : T) :=
  cons T x (nil T).

(** Fortunately, we can avoid providing arguments when Coq has enough
    information to figure them out. In the example below, since [x]
    has type [T], Coq can infer that the type argument for [cons] and
    [nil] must be [T] too. Hence, we can just write a wildcard "_"
    instead of [T], which has the effect of asking Coq to figure out
    what to put there on its own: *)

Definition singleton_list' (T : Type) (x : T) :=
  cons _ x (nil _).

(* We can also instruct Coq once and for all to try to infer arguments
   on its own. This feature is called _implicit arguments_.

   We use "Arguments" to say which arguments of a definition are
   implicit (by surrounding them with curly braces {...}). We can also
   declare them as implicit at definition time: *)

Arguments nil {T}.
Arguments cons {T} _ _.
Definition singleton_list'' {T} (x : T) :=
  cons x nil.

Check (singleton_list'' 3).

(** Finally, we can turn off implicit argument inference for a
    definition locally, by prepending its name with a "@" sign: *)

Check (@singleton_list'' nat).

(** In Coq, polymorphism appears on the type of programs as a
    universal quantifier [forall]: *)

Check @singleton_list''.
Check @nil.

Notation "h :: t" := (cons h t) (at level 60, right associativity).
Notation "[ ]" := (nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Exercise: Define "snoc", which adds an element to the end of a list. *)

Fixpoint snoc {T} (l : list T) (x : T) : list T :=
  [] (* Fill in here *).

Fixpoint app {T} (l1 l2 : list T) : list T :=
  match l1 with
  | [] => l2
  | h :: l1' => h :: (app l1' l2)
  end.

Notation "l1 ++ l2" := (app l1 l2) (at level 60, right associativity).

(** Let us prove some simple facts about lists. To perform an
    inductive proof on a list, we also use the [induction] tactic;
    this has the effect of giving us an inductive hypothesis about the
    tail of the list. Notice that in the proof below we have to give
    names both to the head and to the tail of [l1] *)

Lemma app_assoc :
  forall T (l1 l2 l3 : list T),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros T l1 l2 l3.
  induction l1 as [|h1 t1 IH].
  - (* [] *)
    simpl.
    reflexivity.
  - (* h1 :: t1 *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(* Exercise *)

Lemma snoc_app :
  forall T (l : list T) (x : T),
    snoc l x = l ++ [x].
Proof.
  (* Fill in here *)
Admitted.

End List.

(** Lists, of course, are also defined in the standard library. *)

Require Import Coq.Lists.List.
Import ListNotations.

(** Notice that the definition of rev (list reversal) given in the
    standard library runs in quadratic time. *)

Print rev. (* [C-c C-a C-p] in Proof General *)

(** This is a tail-recursive equivalent that runs in linear time. *)

Fixpoint tr_rev_aux {T} (l acc : list T) : list T :=
  match l with
  | [] => acc
  | x :: l => tr_rev_aux l (x :: acc)
  end.

Definition tr_rev {T} (l: list T) := tr_rev_aux l [].

(** Here, [acc] is an accumulator argument that holds the portion of
    the list that we have reversed so far. Let's prove that [tr_rev]
    is equivalent to [rev]. For this we will need another tactic:


    New Tactic
    ----------

    - [unfold]: Calling [unfold foo] expands the definition of [foo]
      in the goal.
*)

Lemma tr_rev_correct_try_one :
  forall T (l : list T),
    tr_rev l = rev l.
Proof.
  intros T l.
  unfold tr_rev.
  induction l as [| h t IH].
  + simpl.
    reflexivity.
  + simpl.
    (* and now we're stuck... *)
Abort.

(** The problem is that the result we are trying to prove is not
    general enough. We will need the following auxiliary lemma: *)

Lemma tr_rev_aux_correct :
  forall T (l1 l2 : list T),
    tr_rev_aux l1 l2 = rev l1 ++ l2.
Proof.
  intros T l1 l2.
  induction l1 as [|x l1 IH].
  - simpl. reflexivity.
  - simpl.

(** Our inductive hypothesis is too weak to proceed. We want
    [tr_rev_aux l1 l2 = rev l1 ++ l2] for all [l2]. Let's try again
    from the start. *)

Restart.
  intros T l1. (* Now we don't introduce l2, leaving it general. *)
  induction l1 as [|x l1 IH].
  - intros l2. simpl. reflexivity.
  - intros l2. (* Behold our induction hypothesis! *)
    simpl.
    rewrite IH.

(** We can use the [SearchAbout] command to look up lemmas that can be
    used with certain expressions ([C-c C-a C-a] in Proof General). *)

    SearchAbout (_ ++ _ ++ _).
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

(** Our result follows easily: *)

Lemma tr_rev_correct :
  forall T (l : list T),
    tr_rev l = rev l.
Proof.
  intros T l.
  unfold tr_rev.
  rewrite tr_rev_aux_correct.
  SearchAbout (_ ++ []).
  apply app_nil_r.
Qed.

(* ###################################################################### *)
(** * Case study: Red-Black Trees *)

Open Scope bool_scope.
Require Import Coq.Arith.Arith_base.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Psatz.

(** We will now see how we can use Coq's language to implement an
    interesting functional program: a red-black tree module. Red-black
    trees are binary search trees that use an intricate invariant to
    guarantee that they are well-balanced.

    We use Coq's [Section] mechanism to state our definitions within
    the scope of common parameters. This makes our notation lighter by
    avoiding having to redeclare these arguments in all definitions.

    Our definitions are parameterized by a type [A] and a comparison
    function [comp] between elements of [A]. The [comparison] type is
    defined in the standard library, and includes the values [Lt],
    [Gt], and [Eq]. Notice that we state a few hypotheses that are
    needed for our results to hold. *)

Section RedBlack.

Variable A : Type.
Variable comp : A -> A -> comparison.

Hypothesis comp_opp :
  forall x y, comp x y = CompOpp (comp y x).
Hypothesis comp_refl_iff :
  forall x y, comp x y = Eq <-> x = y.
Hypothesis comp_trans :
  forall x y z, comp x y = Lt ->
                comp y z = Lt ->
                comp x z = Lt.

(* Exercise *)
Lemma comp_refl : forall x, comp x x = Eq.
Proof.
  intros x.
  apply comp_refl_iff.
  reflexivity.
Qed.

(** Red-black trees are binary trees that contain elements of [A] on
    their internal nodes, and such that every internal node is colored
    with either [Red] or [Black]. *)

Inductive color := Red | Black.

Inductive tree :=
| Leaf : tree
| Node : color -> tree -> A -> tree -> tree.

(** Before getting into details about the red-black invariants, we can
    already define a search algorithm that looks up an element [x] of
    [A] on a tree. Its definition is standard: *)

Fixpoint member x t : bool :=
  match t with
  | Leaf => false
  | Node _ t1 x' t2 =>
    match comp x x' with
    | Lt => member x t1
    | Eq => true
    | Gt => member x t2
    end
  end.

(** We want to formulate a specification for our algorithm and prove
    that this implementation indeed satisfies it. We begin by
    formalizing what it means for a tree to be a binary search
    tree. This will require the following higher-order function, which
    tests whether all elements of a tree [t] satisfy a property [f]: *)

Fixpoint all (f : A -> bool) (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node _ t1 x t2 => all f t1 && f x && all f t2
  end.

(** We can now state the familiar binary-tree search invariant: Each
    element [x] on an internal node is strictly greater than those to
    its left, and strictly smaller than those to its right. *)

Definition ltb x y :=
  match comp x y with
  | Lt => true
  | _ => false
  end.

Fixpoint search_tree (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node _ t1 x t2 =>
    all (fun y => ltb y x) t1
    && all (ltb x) t2
    && search_tree t1
    && search_tree t2
  end.

(** The specification of [member] is given in terms of a function
    [occurs] that looks for an element [x] on all nodes of a tree [t]. *)

Definition eqb x y :=
  match comp x y with
  | Eq => true
  | _ => false
  end.

Fixpoint occurs (x : A) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node _ t1 y t2 => occurs x t1 || eqb x y || occurs x t2
  end.

(* Exercise? *)
Lemma all_weaken :
  forall f g,
    (forall x, f x = true -> g x = true) ->
    forall t, all f t = true -> all g t = true.
Proof.
  intros f g Hfg t.
  induction t as [|c t1 IH1 x t2 IH2]; simpl; trivial.
  intros H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[H1 H2] H3].
  rewrite IH1; trivial.
  rewrite IH2; trivial.
  rewrite Hfg; trivial.
Qed.

Lemma none_occurs :
  forall x f t,
    f x = false ->
    all f t = true ->
    occurs x t = false.
Proof.
  intros x f t Hfx.
  induction t as [|c t1 IH1 y t2 IH2]; simpl; trivial.
  rewrite Bool.andb_true_iff, Bool.andb_true_iff.
  intros [[H1 H2] H3].
  rewrite IH1; trivial. simpl.
  rewrite IH2; trivial.
  unfold eqb.
  destruct (comp x y) eqn:Hxy; trivial.
  apply comp_refl_iff in Hxy.
  rewrite <- Hxy, Hfx in H2.
  congruence.
Qed.

Lemma member_correct :
  forall x t,
    search_tree t = true ->
    member x t = occurs x t.
Proof.
  intros x t.
  induction t as [|c t1 IH1 y t2 IH2]; simpl; trivial.
  repeat rewrite Bool.andb_true_iff.
  intros [[[H1 H2] H3] H4].
  unfold eqb.
  rewrite IH1; trivial.
  rewrite IH2; trivial.
  assert (Hx : ltb x x = false).
  { unfold ltb. rewrite comp_refl. reflexivity. }
  destruct (comp x y) eqn:Hxy.
  - rewrite Bool.orb_true_r. reflexivity.
  - assert (H2' : all (ltb x) t2 = true).
    { apply (all_weaken (ltb y) (ltb x)); trivial.
      intros z.
      unfold ltb.
      destruct (comp y z) eqn:Hyz; try congruence.
      rewrite (comp_trans _ _ _ Hxy Hyz).
      reflexivity. }
    rewrite (none_occurs x (ltb x) t2 Hx H2').
    destruct (occurs x t1); reflexivity.
  - assert (Hxy' : comp y x = Lt).
    { rewrite comp_opp, Hxy. reflexivity. }
    assert (H1' : all (fun z => ltb z x) t1 = true).
    { apply (all_weaken (fun z => ltb z y) (fun z => ltb z x)); trivial.
      intros z.
      unfold ltb.
      destruct (comp z y) eqn:Hyz; try congruence.
      rewrite (comp_trans _ _ _ Hyz Hxy').
      reflexivity. }
    rewrite (none_occurs x (fun z => ltb z x) t1 Hx H1').
    reflexivity.
Qed.

Definition tree_color (t : tree) : color :=
  match t with
  | Leaf => Black
  | Node c _ _ _ => c
  end.

Fixpoint well_colored (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node c t1 _ t2 =>

    let colors_ok :=
      match c, tree_color t1, tree_color t2 with
      | Red, Black, Black => true
      | Red, _, _ => false
      | Black, _, _ => true
      end in
    colors_ok && well_colored t1 && well_colored t2
  end.

Fixpoint black_height (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node Red t _ _ => black_height t
  | Node Black t _ _ => S (black_height t)
  end.

Fixpoint height_ok (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node _ t1 _ t2 =>
    beq_nat (black_height t1) (black_height t2)
    && height_ok t1
    && height_ok t2
  end.

Definition is_red_black (t : tree) : bool :=
  well_colored t && height_ok t.

Fixpoint size (f : nat -> nat -> nat) (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ t1 _ t2 => S (f (size f t1) (size f t2))
  end.

(** Note that [size plus] computes the number of elements stored in
    the tree. [size max] computes the height of the tree, whereas
    [size min] computes the length of the shortest path from the root
    of the tree to a leaf. *)

Lemma size_min_black_height :
  forall t,
    if height_ok t then black_height t <= size min t
    else True.
Proof.
  intros t.
  induction t as [|c t1 IH1 x t2 IH2].
  + simpl. lia. (* Talk about lia? *)
  + simpl.
    destruct (beq_nat (black_height t1) (black_height t2)) eqn:e12; simpl; trivial.
    rewrite beq_nat_true_iff in e12.
    destruct (height_ok t1); simpl; trivial. (* Talk about semicolons? *)
    destruct (height_ok t2); simpl; trivial.
    destruct c; lia.
Qed.

Lemma size_max_black_height :
  forall t,
    if is_red_black t then
      match tree_color t with
      | Red => size max t <= 2 * black_height t + 1
      | Black => size max t <= 2 * black_height t
      end
    else True.
Proof.
  intros t. unfold is_red_black.
  induction t as [|c t1 IH1 x t2 IH2]; simpl.
  - lia.
  - destruct c.
    + destruct (tree_color t1); simpl; trivial.
      destruct (tree_color t2); simpl; trivial.
      destruct (well_colored t1); simpl; trivial.
      destruct (well_colored t2); simpl; trivial.
      destruct (beq_nat (black_height t1) (black_height t2)) eqn:e12; simpl; trivial.
      rewrite beq_nat_true_iff in e12.
      destruct (height_ok t1); simpl; trivial.
      destruct (height_ok t2); simpl; trivial.
      simpl in *. lia.
    + destruct (well_colored t1); simpl; trivial.
      destruct (well_colored t2); simpl; trivial.
      destruct (beq_nat (black_height t1) (black_height t2)) eqn:e12; simpl; trivial.
      rewrite beq_nat_true_iff in e12.
      destruct (height_ok t1); simpl; trivial.
      destruct (height_ok t2); simpl; trivial.
      assert (H1 : size max t1 <= 2 * black_height t1 + 1).
      { destruct (tree_color t1); simpl in *; lia. }
      assert (H2 : size max t2 <= 2 * black_height t2 + 1).
      { destruct (tree_color t2); simpl in *; lia. }
      lia.
Qed.

Lemma size_max_size_min :
  forall t,
    if is_red_black t then size max t <= 2 * size min t + 1
    else True.
Proof.
  intros t.
  assert (Hmax := size_max_black_height t).
  assert (Hmin := size_min_black_height t).
  unfold is_red_black in *.
  destruct (well_colored t); trivial.
  destruct (height_ok t); trivial.
  simpl in *.
  assert (Hmax' : size max t <= 2 * black_height t + 1).
  { destruct (tree_color t); lia. }
  lia.
Qed.

Lemma size_min_size_plus :
  forall t,
    2 ^ size min t <= size plus t + 1.
Proof.
  intros t.
  induction t as [|c t1 IH1 x t2 IH2]; simpl.
  - lia.
  - assert (H1 : 2 ^ min (size min t1) (size min t2)
                 <= 2 ^ size min t1).
    { apply Nat.pow_le_mono_r; lia. }
    assert (H2 : 2 ^ min (size min t1) (size min t2)
                 <= 2 ^ size min t2).
    { apply Nat.pow_le_mono_r; lia. }
    lia.
Qed.


Definition balance_black_left tl x tr : tree :=
  match tl, x, tr with
  | Node Red (Node Red t1 x1 t2) x2 t3, x3, t4
  | Node Red t1 x1 (Node Red t2 x2 t3), x3, t4 =>
    Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4)
  | _, _, _ => Node Black tl x tr
  end.

Lemma case_balance_black_left :
  forall {T} (f : tree -> T),
    (forall t1 x1 t2 x2 t3 x3 t4,
       f (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
       = f (Node Black (Node Red (Node Red t1 x1 t2) x2 t3) x3 t4)) ->
    (forall t1 x1 t2 x2 t3 x3 t4,
       f (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
       = f (Node Black (Node Red t1 x1 (Node Red t2 x2 t3)) x3 t4)) ->
    forall t1 x t2,
      f (balance_black_left t1 x t2)
      = f (Node Black t1 x t2).
Proof.
  intros T f H1 H2 t1 x t2.
  destruct t1 as [|[] [|[]] ? [|[]]]; simpl; trivial.
Qed.

Definition balance_black_right tl x tr : tree :=
  match tl, x, tr with
  | t1, x1, Node Red (Node Red t2 x2 t3) x3 t4
  | t1, x1, Node Red t2 x2 (Node Red t3 x3 t4) =>
    Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4)
  | _, _, _ => Node Black tl x tr
  end.

Lemma case_balance_black_right :
  forall {T} (f : tree -> T),
    (forall t1 x1 t2 x2 t3 x3 t4,
       f (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
       = f (Node Black t1 x1 (Node Red (Node Red t2 x2 t3) x3 t4))) ->
    (forall t1 x1 t2 x2 t3 x3 t4,
       f (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
       = f (Node Black t1 x1 (Node Red t2 x2 (Node Red t3 x3 t4)))) ->
    forall t1 x t2,
      f (balance_black_right t1 x t2)
      = f (Node Black t1 x t2).
Proof.
  intros T f H1 H2 t1 x t2.
  destruct t2 as [|[] [|[]] ? [|[]]]; simpl; trivial.
Qed.

Definition balance_left c t1 x t2 : tree :=
  match c with
  | Red => Node c t1 x t2
  | Black => balance_black_left t1 x t2
  end.

Definition balance_right c t1 x t2 : tree :=
  match c with
  | Red => Node c t1 x t2
  | Black => balance_black_right t1 x t2
  end.

Lemma black_height_balance_left :
  forall c t1 x t2,
    black_height (balance_left c t1 x t2)
    = black_height (Node c t1 x t2).
Proof.
  intros [] t1 x t2; trivial; simpl.
  rewrite case_balance_black_left; reflexivity.
Qed.

Lemma black_height_balance_right :
  forall c t1 x t2,
    black_height (balance_right c t1 x t2)
    = black_height (Node c t1 x t2).
Proof.
  intros [] t1 x t2; trivial; simpl.
  rewrite case_balance_black_right; reflexivity.
Qed.

Lemma height_ok_balance_left :
  forall c t1 x t2,
    height_ok (balance_left c t1 x t2)
    = height_ok (Node c t1 x t2).
Proof.
  intros [] t1 x t2; trivial.
  apply case_balance_black_left.
  - clear t1 x t2.
    intros t1 x1 t2 x2 t3 x3 t4. admit.
  - clear t1 x t2.
    intros t1 x1 t2 x2 t3 x3 t4. admit.
Qed.

Lemma height_ok_balance_right :
  forall c t1 x t2,
    height_ok (balance_right c t1 x t2)
    = height_ok (Node c t1 x t2).
Proof.
  intros [] t1 x t2; trivial.
  apply case_balance_black_right.
  - clear t1 x t2.
    intros t1 x1 t2 x2 t3 x3 t4. admit.
  - clear t1 x t2.
    intros t1 x1 t2 x2 t3 x3 t4. admit.
Qed.

Fixpoint insert_aux x t : tree :=
  match t with
  | Leaf => Node Red Leaf x Leaf
  | Node c t1 x' t2 =>
    match comp x x' with
    | Eq => t (* Element was already present *)
    | Lt => balance_left c (insert_aux x t1) x' t2
    | Gt => balance_right c t1 x' (insert_aux x t2)
    end
  end.

Definition make_black t : tree :=
  match t with
  | Leaf => Leaf
  | Node _ t1 x t2 => Node Black t1 x t2
  end.

Definition insert x t : tree :=
  make_black (insert_aux x t).

Definition almost_well_colored t : bool :=
  match t with
  | Leaf => true
  | Node _ t1 _ t2 => well_colored t1 && well_colored t2
  end.

Lemma well_colored_weaken :
  forall t,
    well_colored t = true ->
    almost_well_colored t = true.
Proof.
  intros t.
  destruct t as [|[] t1 x t2]; simpl; trivial.
  destruct (tree_color t1); simpl; try discriminate.
  destruct (tree_color t2); simpl; try discriminate.
  trivial.
Qed.

Lemma black_height_insert_aux :
  forall x t,
    black_height (insert_aux x t)
    = black_height t.
Proof.
  intros x t.
  induction t as [|c t1 IH1 x' t2 IH2]; trivial.
  simpl. destruct (comp x x'); trivial.
  - rewrite black_height_balance_left. simpl.
    rewrite IH1.
    reflexivity.
  - rewrite black_height_balance_right. simpl.
    reflexivity.
Qed.

Lemma height_ok_insert_aux :
  forall x t,
    height_ok (insert_aux x t)
    = height_ok t.
Proof.
  induction t as [|c t1 IH1 x' t2 IH2]; trivial.
  simpl. destruct (comp x x'); trivial.
  - rewrite height_ok_balance_left. simpl.
    rewrite IH1, black_height_insert_aux.
    reflexivity.
  - rewrite height_ok_balance_right. simpl.
    rewrite IH2, black_height_insert_aux.
    reflexivity.
Qed.

Lemma height_ok_make_black :
  forall t,
    height_ok (make_black t) = height_ok t.
Proof. intros [|c t1 x t2]; reflexivity. Qed.

Lemma almost_well_colored_make_black :
  forall t, well_colored (make_black t) = almost_well_colored t.
Proof. intros [|c t1 x t2]; reflexivity. Qed.

Lemma well_colored_balance_black_left :
  forall t1 x t2,
    almost_well_colored t1 = true ->
    well_colored (balance_black_left t1 x t2)
    = well_colored t2.
Proof.
  intros t1 x t2.
  refine (match t1 with
          | Node Red (Node Red _ _ _) _ _ => _
          | Node Red _ _ (Node Red _ _ _) => _
          | _ => _
          end); simpl; try reflexivity.
  - destruct (tree_color t3), (tree_color t4); try discriminate; simpl.
    rewrite Bool.andb_assoc. intros H. rewrite H. reflexivity.
  - intros H. rewrite H. reflexivity.
  - destruct (tree_color t3), (tree_color t4); try discriminate; simpl.
    rewrite Bool.andb_assoc. intros H. rewrite H. reflexivity.
  - intros H. rewrite H. reflexivity.
  - destruct (tree_color t5), (tree_color t6); try (rewrite Bool.andb_false_r; discriminate).
    repeat rewrite Bool.andb_assoc.
    rewrite Bool.andb_true_r. simpl. intros H. rewrite H. reflexivity.
  - intros H. rewrite H. reflexivity.
  - intros H. rewrite H. reflexivity.
Qed.

Lemma well_colored_balance_black_right :
  forall t1 x t2,
    almost_well_colored t2 = true ->
    well_colored (balance_black_right t1 x t2)
    = well_colored t1.
Proof.
  intros t1 x t2.
  refine (match t2 with
          | Node Red (Node Red _ _ _) _ _ => _
          | Node Red _ _ (Node Red _ _ _) => _
          | _ => _
          end); simpl; try reflexivity.
  - intros _. apply Bool.andb_true_r.
  - intros _. apply Bool.andb_true_r.
  - destruct (tree_color t3), (tree_color t4); try discriminate; simpl.
    rewrite Bool.andb_true_r. intros H. rewrite H, Bool.andb_true_r. reflexivity.
  - intros H. rewrite H, Bool.andb_true_r. reflexivity.
  - destruct (tree_color t3), (tree_color t4); try discriminate; simpl.
    repeat rewrite <- Bool.andb_assoc. intros H. rewrite H, Bool.andb_true_r. reflexivity.
  - intros H. rewrite H, Bool.andb_true_r. reflexivity.
  - destruct (tree_color t5), (tree_color t6); try (rewrite Bool.andb_false_r; discriminate).
    repeat rewrite <- Bool.andb_assoc. simpl.
    intros H. rewrite H, Bool.andb_true_r. reflexivity.
  - intros H. rewrite H, Bool.andb_true_r. reflexivity.
  - intros H. rewrite H, Bool.andb_true_r. reflexivity.
Qed.

Lemma well_colored_insert_aux :
  forall x t,
    if well_colored t then
      match tree_color t with
      | Red => almost_well_colored (insert_aux x t)
      | Black => well_colored (insert_aux x t)
      end = true
    else True.
Proof.
  intros x t.
  induction t as [|[] t1 IH1 x' t2 IH2]; trivial; simpl.
  - reflexivity.
  - destruct (tree_color t1); simpl; trivial.
    destruct (tree_color t2); simpl; trivial.
    destruct (comp x x'); simpl.
    + destruct (well_colored t1 && well_colored t2); trivial.
    + destruct (well_colored t1); simpl; trivial.
      destruct (well_colored t2); simpl; trivial.
      rewrite IH1. reflexivity.
    + destruct (well_colored t1); simpl; trivial.
  - destruct (comp x x'); simpl.
    + destruct (well_colored t1 && well_colored t2); trivial.
    + destruct (well_colored t1); simpl; trivial.
      assert (IH1' : almost_well_colored (insert_aux x t1) = true).
      { destruct (tree_color t1); trivial.
        apply well_colored_weaken. trivial. }
      rewrite well_colored_balance_black_left; trivial.
      destruct (well_colored t2); trivial.
    + rewrite Bool.andb_comm.
      destruct (well_colored t2); simpl; trivial.
      assert (IH1' : almost_well_colored (insert_aux x t2) = true).
      { destruct (tree_color t2); trivial.
        apply well_colored_weaken. trivial. }
      rewrite well_colored_balance_black_right; trivial.
      destruct (well_colored t1); trivial.
Qed.

Lemma is_red_black_insert :
  forall x t,
    if is_red_black t then
      is_red_black (insert x t) = true
    else True.
Proof.
  intros x t.
  unfold insert, is_red_black.
  assert (H1 := well_colored_insert_aux x t).
  assert (H2 := height_ok_insert_aux x t).
  rewrite height_ok_make_black.
  rewrite H2.
  rewrite almost_well_colored_make_black.
  destruct (well_colored t); simpl; trivial.
  destruct (tree_color t).
  - rewrite H1. destruct (height_ok t); trivial.
  - rewrite well_colored_weaken; trivial.
    destruct (height_ok t); trivial.
Qed.

End RedBlack.

(* ###################################################################### *)
(** * Dependently Typed Programming *)

Definition stack := list.

Definition push {T} (x:T) (s : stack T) : stack T  := x :: s.

Fail Definition pop {T} (s : stack T) : T * stack T :=
  match s with
  | h :: t => (h, t)
  (* What do we do for an empty stack? *)
  end.

(** Traditional approach: Use an [option] type. *)

Definition pop {T} (s : stack T) : option T * stack T :=
  match s with
  | nil => (None, s)
  | h :: t => (Some h, t)
  end.

(* We can avoid having to use (and check) option types by defining a
   size-indexed stack. *)

Inductive istack (T : Type) : nat -> Type :=
  | empty : istack T O
  | add :  forall n, T -> istack T n -> istack T (S n).

Arguments empty {T}.
Arguments add {T} {n} _ _.

Definition ipush {T} {n:nat} (x:T) (s : istack T n) : istack T (S n) := add x s.

Check add.

Definition ipop {T} {n} (s : istack T (S n)) : T * istack T n :=
  match s with
  | add _ top bottom => (top, bottom)
  end.

Fixpoint combine {T} {n1} {n2} (s1 : istack T n1) (s2 : istack T n2) :
  istack T (n1 + n2) :=
    match s1 with
    | empty => s2
    | add _ x s1' => add x (combine s1' s2)
    end.

(* Exercise: Write a snoc function to add an element to the bottom of
   an indexed stack. Do not use the combine function (in this case, it will make
   life difficult.) *)
