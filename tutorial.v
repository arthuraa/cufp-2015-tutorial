(* ###################################################################### *)
(** * Syntax *)

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
    [inversion] tactic to prune that subgoal.

    New tactics
    -----------

    - [inversion]: If hypothesis [H] states that [e1 = e2], where [e1]
      and [e2] are expressions that start with different
      constructors, than [inversion H] completes the current subgoal.

*)

Lemma eq_beq_nat :
  forall m n, beq_nat m n = true -> m = n.
Proof.
  intros m.
  induction m as [|m IH].
  - intros k. destruct k as [|].
    + reflexivity.
    + simpl. intros H. inversion H.
  - intros k. destruct k as [|k].
    + simpl. intros H. inversion H.
    + simpl. intros H. rewrite (IH k).
      * reflexivity.
      * apply H.
Qed.

(** (Notice that we rewrote using [IH] we specified which value of [n]
    to use (in this case, [k]) by writing [IH k].) *)

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

(* This is a tail-recursive equivalent that runs in linear time *)

Fixpoint tr_rev' {T} (l acc : list T) : list T :=
  match l with
  | [] => acc
  | x :: l => tr_rev' l (x :: acc)
  end.

(* Here, acc is an accumulator argument that holds the portion of the
list that we have reversed so far. Prove that tr_rev is equivalent to
rev: *)

Definition tr_rev {T} (l: list T) := tr_rev' l [].

(* Tactic unfold *)

Lemma tr_rev_correct_try_one :
  forall T (l : list T),
    tr_rev l = rev l.
Proof.
  intros T l.
  induction l as [| h t IH].
  + simpl.
    unfold tr_rev.
    simpl.
    reflexivity.
  + unfold tr_rev in *. (* "in *" allows us to apply a rewrite or unfold globally *)
    simpl.
    (* and now we're stuck... *)
Admitted.

(* We need an auxiliary lemma to make this go through. We will
   use the following lemmas from the standard library. *)

Lemma tr_rev'_correct :
  forall T (l1 l2 : list T),
    tr_rev' l1 l2 = rev l1 ++ l2.
Proof.
  intros T l1 l2.
  induction l1 as [|x l1 IH].
  - simpl. reflexivity.
  - simpl.
    (* Our inductive hypothesis is too weak to proceed.
       We want tr_rev' l1 l2 = rev l1 ++ l2 for all l2 *)
    (* Let's try again from the start *)
Restart.
  intros T l1. (* Now we don't introduce l2, leaving it general. *)
  induction l1 as [|x l1 IH].
  - intros l2. simpl. reflexivity.
  - intros l2. (* Behold our induction hypothesis! *)
    simpl.
    rewrite IH.
    SearchAbout (_ ++ _ ++ _). (* [C-c C-a C-a] in Proof General *)
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.

(* ###################################################################### *)
(** * Case study: Red-Black Trees *)

Open Scope bool_scope.
Require Import Coq.Arith.Arith_base.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Psatz.

Section RedBlack.

Variable A : Type.
Variable comp : A -> A -> bool.

Inductive color := Red | Black.

Inductive tree :=
| Leaf : tree
| Node : color -> tree -> A -> tree -> tree.

Definition tree_color (t : tree) : color :=
  match t with
  | Leaf => Black
  | Node c _ _ _ => c
  end.

Fixpoint is_red_black_aux (t : tree) : option nat :=
  match t with
  | Leaf => Some 0

  | Node c t1 _ t2 =>
    match is_red_black_aux t1, is_red_black_aux t2 with
    | Some h1, Some h2 =>
      if beq_nat h1 h2 then
        match c with
        | Red => match tree_color t1, tree_color t2 with
                 | Black, Black => Some (S h1)
                 | _, _ => None
                 end
        | Black => Some (S h1)
        end
      else None
    | _, _ => None
    end
  end.

Definition is_red_black (t : tree) : bool :=
  match is_red_black_aux t with
  | Some _ => true
  | None => false
  end.

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
    match is_red_black_aux t with
    | Some h => h <= size min t
    | None => True
    end.
Proof.
  intros t.
  induction t as [|c t1 IH1 x t2 IH2].
  + simpl. lia.
  + simpl.
    destruct (is_red_black_aux t1) as [h1|]; trivial. (* Talk about semicolons? *)
    destruct (is_red_black_aux t2) as [h2|]; trivial.
    destruct (beq_nat h1 h2) eqn:eh1h2; trivial.
    rewrite beq_nat_true_iff in eh1h2.
    rewrite eh1h2 in *.
    destruct c.
    - destruct (tree_color t1); trivial.
      destruct (tree_color t2); trivial.
      lia.
    - lia.
Qed.

Lemma size_max_black_height :
  forall t,
    match is_red_black_aux t with
    | Some h =>
      match tree_color t with
      | Red => size max t <= 2 * h + 1
      | Black => size max t <= 2 * h
      end
    | None => True
    end.
Proof.
  intros t.
  induction t as [|c t1 IH1 x t2 IH2].
  + simpl. lia.
  + simpl.
    destruct (is_red_black_aux t1) as [h1|]; trivial. (* Talk about semicolons? *)
    destruct (is_red_black_aux t2) as [h2|]; trivial.
    destruct (beq_nat h1 h2) eqn:eh1h2; trivial.
    rewrite beq_nat_true_iff in eh1h2.
    rewrite eh1h2 in *.
    destruct c.
    - destruct (tree_color t1); trivial.
      destruct (tree_color t2); trivial.
      lia.
    - assert (H1 : size max t1 <= 2 * h2 + 1).
      { destruct (tree_color t1); lia. }
      assert (H2 : size max t2 <= 2 * h2 + 1).
      { destruct (tree_color t2); lia. }
      lia.
Qed.

Lemma size_max_size_min :
  forall t,
    is_red_black t = true ->
    t <=

Lemma size_min_size_max :
  forall t : tree,
    is_red_black t = true ->
    size max t <= 2 * size min t + 1.
Proof.
  intros t.
  induction t as [|[] t1 IH1 x t2 IH2].
  + simpl. lia.
  + simpl. intros H.
    destruct (tree_color t1), (tree_color t2); try now inversion H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    apply IH1 in H1.
    apply IH2 in H2.

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

Rewriting

Lists (Polymorphism)

Nat-Indexed Stacks

Tactics Cheat Sheet