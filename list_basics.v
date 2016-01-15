(* ###################################################################### *)
(** * Proofs and Programs *)

(** (We use [admit] and [Admitted] to hide solutions from exercises.) *)

Axiom admit : forall {T}, T.

(** FULL: Everything in Coq is built from scratch -- even booleans!
    Fortunately, they are already provided by the Coq standard
    library, but we'll review their definition here to get familiar
    with the basic features of the system. *)

(** [Inductive] is Coq's way of defining an algebraic datatype.  Its
    syntax is similar to OCaml's ([type]) or Haskell's ([data]). Here,
    we define [bool] as a simple algebraic datatype. *)

Module Bool.

Inductive bool : Type :=
(* FULL *)
| true : bool
| false : bool.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

(* EX1 (trivalue) *)
(** Define a three-valued data type, representing ternary logic.  Here
    something can be true, false and unknown. *)

Inductive trivalue : Type :=
(* SOLUTION *)
| tv_true
| tv_false
| tv_unknown
(* /SOLUTION *)
.
(** [] *)

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
(* FULL *)
  match b1, b2 with
  | false, false => false
  | _, _ => true
  end.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

Print orb.

(** We can also use an [if] statement, which matches on the first
    constructor of any two-constructor datatype, in our definition. *)

Definition andb (b1 b2: bool) : bool :=
(* FULL *)
  if b1 then b2 else false.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

(** Let's test our functions. The [Compute] command tells Coq to
    evaluate an expression and print the result on the screen.*)

Compute (negb true).
Compute (orb true false).
Compute (andb true false).

(* EX1 (xor) *)
(** Define xor (exclusive or). *)

Definition xorb (b1 b2 : bool) : bool :=
(* ADMIT *) if b1 then negb b2 else b2. (* /ADMIT *)

Compute (xorb true true).
(** [] *)


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

(* EX1 (orb_true_l) *)
Theorem orb_true_l :
  forall b, orb true b = true.
Proof.
(* ADMITTED *)
  reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

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
(* WORKINCLASS *)
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
(* /WORKINCLASS *)

(** We can call [destruct] as many times as we want, generating deeper subgoals. *)

Theorem andb_commutative : forall b1 b2 : bool, andb b1 b2 = andb b2 b1.
Proof.
(* WORKINCLASS *)
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
(* /WORKINCLASS *)

(* EX1 (andb_false_r) *)
(** Show that b AND false is always false  *)

Theorem andb_false_r :
(* ADMIT *)
  forall b, andb b false = false.
(* /ADMIT *)
Proof.
(* ADMITTED *)
  intros b. destruct b.
  + reflexivity.
  + reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1 (xorb_b_neg_b) *)
(** Show that b xor (not b) is always true. *)

Theorem xorb_b_neg_b :
(* ADMIT *)
  forall b, xorb b (negb b) = true.
(* /ADMIT *)
Proof.
(* ADMITTED *)
  intros b. destruct b.
  + reflexivity.
  + reflexivity.
Qed.
(* /ADMITTED *)

(** Sometimes, we want to show a result that requires hypotheses. In
    Coq, [P -> Q] means that [P] implies [Q], or that [Q] is true
    whenever [P] is. We can use [->] multiple times to express that
    more than one hypothesis are needed; the syntax is similar to how
    we write multiple-argument functions in OCaml or Haskell. For
    example: *)

Theorem rewrite_example : forall b1 b2 b3 b4,
  b1 = b4 ->
  b2 = b3 ->
  andb b1 b2 = andb b3 b4.

(** FULL: We can use the [intros] tactic to give hypotheses names,
    bringing them into the proof context. *)

Proof.
(* FULL *)
  intros b1 b2 b3 b4 eq14 eq23.
(* /FULL *)

(** FULL: Now, our context has two hypotheses: [eq14], which states
    that [b1 = b4], and [eq23], stating that [b2 = b3]. *)

(** Here are some tactics for using hypotheses and previously proved
    results:


    New tactics
    -----------

    - [rewrite]: Replace one side of an equation by the other.

    - [apply]: Suppose that the current goal is [Q]. If [H : Q], then
      [apply H] solves the goal. If [H : P -> Q], then [apply H]
      replaces [Q] by [P] in the goal. If [H] has multiple hypotheses,
      [H : P1 -> P2 -> ... -> Pn -> Q], then [apply H] generates one
      subgoal for each [Pi]. *)

(* FULL *)
  rewrite eq14. (* replace b1 with b4 in the goal *)
  rewrite <- eq23. (* replace b3 with b2 in the goal. *)
  apply andb_commutative. (* solve using our earlier theorem *)
(* /FULL *)
(* TERSE: WORK IN CLASS *)
Qed.


(* EX1 (xorb_same) *)
(** Show that if [b1 = b2] then [xorb b1 b2] is equal to [false]. *)

Theorem xorb_same :
(* ADMIT *)
  forall b1 b2, b1 = b2 -> xorb b1 b2 = false.
(* /ADMIT *)
Proof.
(* ADMITTED *)
  intros b1 b2 e.
  rewrite e.
  destruct b2.
  + reflexivity.
  + reflexivity.
Qed.
(* /ADMITTED *)

End Bool.


(* ###################################################################### *)

(** We will use the following option to make polymorphism more
    convenient. *)

Set Implicit Arguments.

(** * Lists

    We will now shift gears and study more interesting functional
    programs; namely, programs that manipulate _lists_. *)

Module List.

(** Here's a polymorphic definition of a [list] type in Coq: *)

Inductive list (T : Type) :=
| nil : list T
| cons : T -> list T -> list T.

(** Here's how we define a function to append two lists.
    Note that we declare the type parameter T. *)

Fixpoint app T (l1 l2 : list T) : list T :=
(* FULL *)
  match l1 with
  | nil => l2
  | cons h t  => cons h (app t l2)
  end.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

(** Coq comes with a syntax extension mechanism for defining custom
    notations. Without getting into details, here's how we can give
    familiar syntax for lists. *)

Notation "h :: t" := (cons h t) (at level 60, right associativity).
Notation "[ ]" := (nil _).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y [] ) ..).
Notation "l1 ++ l2" := (app l1 l2) (at level 60, right associativity).

(** Since [nil] can potentially be of any type, we add an underscore
    to tell Coq to infer the type from the context. *)

(** We can now check the types of expressions involving lists. *)

Check [].
Check true :: [].
Check [true ; false].
Check [true ; false] ++ [false].

(** And compute the last. *)
Compute [true ; false] ++ [false].

(** Note that we can use define notations and functions
    simultaneously: *)

Reserved Notation "l1 @ l2" (at level 60).
Fixpoint app' T (l1 l2 : list T) : list T :=
  match l1 with
  | [] => l2
  | h :: t  => h :: (t @ l2)
  end

  where "l1 @ l2" := (app' l1 l2).


(* EX1 (snoc) *)
(** Define [snoc], which adds an element to the end of a list. *)

Fixpoint snoc {T} (l : list T) (x : T) : list T :=
(* ADMIT *)
  match l with
  | [] => [x]
  | h :: t => h :: snoc t x
  end.
(* /ADMIT *)

(** It is easy to show that appending [nil] to the left of a list
    yields the original list.  *)

Lemma app_nil_l: forall T (l : list T), [] ++ l  = l.
Proof.
(* WORKINCLASS *)
  intros T l.
  simpl.
  reflexivity.
Qed.
(* /WORKINCLASS *)

(** Showing the symmetric result is more difficult
    since it doesn't follow by simplification alone. *)

Lemma app_nil_r: forall T (l : list T), l ++ []  = l.
Proof.
(* FULL *)
  intros T l.
  simpl. (* Does nothing *)
  destruct l as [| h t]. (* Notice the [as] clause, which allows us
                            to name constructor arguments. *)
  + simpl.
    reflexivity.
  + simpl. (* no way to proceed... *)
(* /FULL *)

(** FULL: The problem is that we can only prove the result for [h::t]
    if we already know that it is valid for [t]. We need a bigger
    hammer here... *)

(** New tactic
    ----------

    - [induction]: Argue by induction. It works as [destruct], but
    additionally giving us an inductive hypothesis in the inductive
    case. *)
(* FULL *)
Restart.
  intros T l.
  induction l as [| h t IH]. (* Note the additional name [IH], given to our
                                inductive hypothesis *)
  + simpl.
    reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
Qed.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

(** As a rule of thumb, when proving some property of a recursive
    function, it is a good idea to do induction on the recursive
    argument of the function. For instance, let's show that [app] is
    associative: *)

Lemma app_assoc :
  forall T (l1 l2 l3 : list T),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
(* WORKINCLASS *)
  intros T l1 l2 l3.
  induction l1 as [|h1 t1 IH]. (* l1 is the right choice here, since [app] is defined
                                  by recursion on the first argument. *)
  - (* [] *)
    simpl.
    reflexivity.
  - (* h1 :: t1 *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.
(* /WORKINCLASS *)

(** Take-home exercise: Try to do induction on [l2] and [l3] in the
    above proof, and see where it fails. *)

(* EX2 (snoc_app) *)
(** Prove that [snoc l x] is equivalent to appending [x] to the end of
    [l]. *)

Lemma snoc_app : forall T (l : list T) (x : T), snoc l x = l ++ [x].
Proof.
(* ADMITTED *)
  intros T l x.
  induction l as [|h t IH].
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(** The natural numbers are defined in Coq's standard library as follows:

    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.

    where [S] stands for "Successor".

    Coq prints [S (S (S O))] as "3", as you might expect.

*)

Set Printing All.

Check 0.
Check 2.
Check 2 + 2.

Unset Printing All.

Check S (S (S O)).
Check 2 + 3.
Compute 2 + 3.

(** Now we can define the [length] function: *)

Fixpoint length T (l : list T) :=
(* FULL *)
  match l with
  | [] => 0
  | h :: t => 1 + length t
  end.
(* FULL *)
(* TERSE: WORK IN CLASS *)

Compute length [1; 1; 1].

(* EX3 (app_length) *)

Lemma app_length : forall T (l1 l2 : list T),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
(* ADMITTED *)
  intros T l1 l2.
  induction l1 as [|h t IH].
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Qed.
(* /ADMITTED *)

(** Often we find ourselves needing to reason about _contradictory_
    hypotheses. Whenever we have a hypothesis that equates two
    expressions that start with different constructors, we can use the
    [discriminate] tactic to prune that subgoal.

    This is a particular case of what is known as _the principle of
    explosion_, which states that a contradiction implies anything.


    New Tactic
    ----------

    - [discriminate]: Looks for an equation between terms starting
      with different constructors, and solves the current goal.

    Let's try to prove that if [l1 ++ l2 = []] then [l1] is [[]]

 *)

Lemma app_eq_nil_l : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l1 = [].
Proof.
(* WORKINCLASS *)
  intros T l1 l2 H.
  destruct l1 as [| h t].
  + (* [] *)
    reflexivity.
  + (* h :: t *)
    simpl in H.
    discriminate.
Qed.
(* /WORKINCLASS *)

(* EX2 (app_eq_nil_r) *)
(** Prove the same about [l2]. *)

Lemma plus_nil_r : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l2 = [].
Proof.
(* ADMITTED *)
  intros T l1 l2 H.
  destruct l1 as [|h t].
  + apply H.
  + discriminate.
Qed.
(* /ADMITTED *)
(** [] *)

(** FULL: Coq, like many other proof assistants, requires functions to
    be _total_ and defined for all possible inputs; in particular,
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
(** TERSE: Note that there are many functions that we cannot write in Coq... *)

Fail Fixpoint shuffle T (l1 l2 : list T) :=
  match l1 with
  | [] => l2
  | h :: t => h :: shuffle l2 t
  end.

(** FULL: The [Fail] keyword instructs Coq to ignore a command when it
    fails, but to fail if the command succeeds. It is useful for
    showing certain pieces of code that are not accepted by the
    language.

    In this case, we can rewrite [shuffle] so that it is accepted by
    Coq's termination checker: *)
(** TERSE: We can easily adapt this function to please Coq. *)
Fixpoint shuffle T (l1 l2 : list T) :=
(* FULL *)
  match l1, l2 with
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: shuffle t1 t2
  | [], _ => l2
  | _, [] => l1
  end.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

Print shuffle.


(** Let's define list reversal function and prove some of its basic
    properties. *)

Fixpoint rev T (l : list T) :=
(* FULL *)
  match l with
  | [] => []
  | h :: t => (rev t) ++ [h]
  end.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

Lemma rev_app : forall T (l1 l2 : list T), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
(* WORKINCLASS *)
  intros T l1 l2.
  induction l1 as [|h t IH].
  + simpl.
    rewrite app_nil_r.
    reflexivity.
  + simpl.
    rewrite IH.
    rewrite app_assoc.
    reflexivity.
Qed.
(* /WORKINCLASS *)

(* EX2 (rev_app) *)
(** Using [rev_app], prove that reversing a list twice results in the
    same list. *)

Lemma rev_involutive : forall T (l : list T), rev (rev l) = l.
Proof.
(* ADMITTED *)
  intros T l. induction l as [|h t IH].
  + reflexivity.
  + simpl. rewrite rev_app. rewrite IH. reflexivity.
Qed.
(* /ADMITTED *)

(** Notice that the definition of list reversal given above runs in
    quadratic time. Here is a tail-recursive equivalent that runs in
    linear time. *)

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

(* FULL *)
Lemma tr_rev_eq_rev_try_one :
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

Lemma tr_rev_aux_eq_rev :
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
(* /FULL *)

Lemma tr_rev_eq_rev :
  forall T (l : list T),
    tr_rev l = rev l.
Proof.
(* WORKINCLASS *)
  intros T l.
  unfold tr_rev.
  rewrite tr_rev_aux_eq_rev.
  SearchAbout (_ ++ []).
  apply app_nil_r.
Qed.
(* /WORKINCLASS *)

End List.


(** You may have noticed that several of the proofs in this section,
    particularly regarding the associativity of the append function,
    closely resemble proofs about arithmetic. You might also be interested
    in Coq for its ability to prove results in mathematics. The
    material in this section should be sufficient for you to start
    formulating theorems about the natural numbers, such as the
    commutativity, associativity and distributivity of addition and
    multiplication.

    You might start from the very beginning by defining the natural
    numbers as follows:

    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.

    From there you can define +, -, *, /, ^ etc. We encourage you to
    start on your own, but to help, we've included a module on the
    natural numbers. We hope you enjoy.

*)
