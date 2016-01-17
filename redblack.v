(* ###################################################################### *)
(** * Case study: Red-Black Trees *)

Open Scope bool_scope.
Require Import Coq.Arith.Arith_base.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Psatz.

(** (We use [admit] and [Admitted] to hide solutions from exercises.) *)

Axiom admit : forall {T : Type}, T.

(** We will now see how we can use Coq's language to implement an
    interesting functional program: a red-black tree module. Red-black
    trees are binary search trees that use an intricate invariant to
    guarantee that they are well-balanced.

    We state our definitions inside of a Coq [Section], which allows
    us parameterize them by the type of elements to be
    stored. Specifically, we use the [Parameter] and [Hypothesis]
    keywords to introduce parameters and hypothesis that can be
    invoked in definitions and lemmas inside the [Section]. *)

Section RedBlack.

(** Our definitions are parameterized by a type [A] and a comparison
    function [comp] between elements of [A]. The [comparison] type is
    defined in the standard library, and represents the result of
    comparing two elements of a totally ordered type. *)

Parameter A : Type.
Parameter comp : A -> A -> comparison.
(* Inductive comparison : Type := Eq | Lt | Gt. *)

(** In order for our definitions to work, we must assume that a few
    properties hold of the [comp] operator. First, we assume that
    [comp] is _transitive_: that is, if [x] is less than [y] and [y]
    is less than [z], then [x] is less than [z]. *)

Hypothesis comp_trans :
  forall x y z, comp x y = Lt ->
                comp y z = Lt ->
                comp x z = Lt.

(** Next, we assume that [comp] is reflexive, and that elements that
    test for [Eq] are equal. *)

Hypothesis comp_refl_iff :
  forall x y, comp x y = Eq <-> x = y.

(** [A <-> B] ("A if and only if B") states that [A] and [B] are
    _logically equivalent_, i.e., that [A] implies [B] and [B] implies
    [A]. It can be applied in either direction with the [apply]
    tactic. It can also be rewritten with [rewrite]. *)

(* EX1 (comp_refl) *)
(** Practice the use of [rewrite] to prove the following. *)

Lemma comp_refl : forall x, comp x x = Eq.
Proof.
(* ADMITTED *)
  intros x. rewrite comp_refl_iff. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(** Finally, we assume that if [x] is less than [y], then [y] is
    greater than [x]. The [CompOpp] function swaps [Lt] and [Gt]. *)

Hypothesis comp_opp :
  forall x y, comp x y = CompOpp (comp y x).

(** Red-black trees are binary search trees that contain elements of
    [A] on their internal nodes, and such that every internal node is
    colored with either [Red] or [Black]. [Leaf] represents an empty
    tree. [Node c left x right] represents an internal node colored
    [c], with children [left] and [right], storing element [x : A]. *)

Inductive color := Red | Black.

Inductive tree :=
| Leaf : tree
| Node : color -> tree -> A -> tree -> tree.

(* EX2 (elements) *)

(** Using the list functions we have already studied, complete the
    definition of the [elements] function below. Your implementation
    should perform an inorder traversal of the elements of [t] and
    accumulate them in a list. *)

Fixpoint elements (t : tree) : list A :=
(* ADMIT *)
  match t with
  | Leaf => []
  | Node _ tl x tr => elements tl ++ x :: elements tr
  end.
(* /ADMIT *)
(** [] *)

(** Before getting into details about the red-black invariants, let's
    study the following function, which looks up an element [x] of [A]
    on a tree. *)

Fixpoint member x t : bool :=
(* FULL *)
  match t with
  | Leaf => false
  | Node _ t1 x' t2 =>
    match comp x x' with
    | Lt => member x t1
    | Eq => true
    | Gt => member x t2
    end
  end.
(* FULL *)
(* TERSE: WORK IN CLASS *)

(* EX1 (member_ex) *)

(** To test your understanding of [member], prove the following
    result. *)

Example member_ex :
  forall x tl y tr,
    member x tl = true ->
    comp x y = Lt ->
    member x (Node Black tl y tr) = true.
Proof.
(* ADMITTED *)
  intros x tl y tr H1 H2.
  simpl. rewrite H2. rewrite H1. reflexivity.
Qed.
(* /ADMITTED *)

(** [] *)

(** We want to state a specification for [member] and prove that it is
    valid. First, we formalize what it means for a tree to be a binary
    search tree. This requires the following function, which tests
    whether a property [f] holds of the elements of a tree [t]: *)

Fixpoint all (f : A -> bool) (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node _ t1 x t2 => all f t1 && f x && all f t2
  end.

(** Let's prove the following simple property of [all], which will
    be useful later. *)

Lemma all_weaken :
  forall f g,
    (forall x, f x = true -> g x = true) ->
    forall t, all f t = true -> all g t = true.
Proof.
  intros f g Hfg t.

(** New tactic
    ----------

    - [trivial]: solves simple goals through [reflexivity] and by
      looking for assumptions in the context that apply directly. If
      it cannot solve the goal, it does nothing. *)

  induction t as [|c t1 IH1 x t2 IH2].
  - trivial.
  - simpl. intros H.

(** FULL: Often, tactics generate multiple subgoals that can be solved
    with simple (or very similar) proofs. We can handle these
    simultaneously using the tactic sequencing operator [;]. *)

(** New Tactics
    -----------

    - [;]: An expression such as [foo; bar] first calls [foo], then
      calls [bar] on all generated subgoals. A common idiom is [foo;
      trivial], which solves the trivial subgoals and does nothing on
      the remaining ones.

    - [try]: Calling [try foo] tries to execute [foo], doing nothing
      if [foo] raises any errors. In particular, if [foo] is a
      _terminating tactic_ such as [discriminate], [try foo] attempts
      to solve the goal, and does nothing if it fails.

    - [destruct ... eqn: ...]: Do case analysis on an expression while
      generating an equation. *)

(* WORKINCLASS *)
    destruct (all f t1) eqn:H1; try discriminate.
    destruct (f x) eqn:H2; try discriminate.
    destruct (all f t1) eqn:H3; try discriminate.
    rewrite IH1; trivial.
    rewrite Hfg; trivial.
    rewrite IH2; trivial.
Qed.
(* /WORKINCLASS *)

(** FULL: We can now state the binary-tree invariant: Each element [x]
    on an internal node is strictly greater than those to its left,
    and strictly smaller than those to its right. The auxiliary
    function [ltb] tests whether an element of [A] is smaller than
    another one. *)
(** TERSE: Let's define the binary-tree invariant. *)

Definition ltb x y :=
  match comp x y with
  | Lt => true
  | _ => false
  end.

Fixpoint search_tree (t : tree) : bool :=
(* FULL *)
  match t with
  | Leaf => true
  | Node _ t1 x t2 =>
    all (fun y => ltb y x) t1
    && all (ltb x) t2
    && search_tree t1
    && search_tree t2
  end.
(* /FULL *)
(* TERSE: WORK IN CLASS *)

(** In order to state the specification of [member], we define a
    function [occurs] that looks up an element [x] on all nodes of a
    tree [t]. The [eqb] function tests whether two elements of [A] are
    equal. *)

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

(* EX2 (eqb_eq) *)

(** Show that [eqb] implies equality. *)

Lemma eqb_eq : forall x y, eqb x y = true -> x = y.
Proof.
(* ADMITTED *)
  intros x y.
  unfold eqb.
  destruct (comp x y) eqn:Hcomp; try discriminate.
  intros _. rewrite comp_refl_iff in Hcomp.
  apply Hcomp.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (none_occurs) *)
(** If [x] is strictly smaller (or bigger) than the elements of a tree
    [t], we know that [x] cannot occur in [t], thanks to the following
    general result. Your job is to prove it and then use it to show
    the [member_prune_right] and [member_prune_left] lemmas below. *)

Lemma none_occurs :
  forall (x : A) (f : A -> bool) (t : tree),
    f x = false ->
    all f t = true ->
    occurs x t = false.
Proof.
(* ADMITTED *)
  intros x f t Hfx Hft.
  induction t as [|c tl IHl x' tr IHr]; simpl; trivial.
  simpl in Hft.
  destruct (all f tl) eqn:Hftl; try discriminate.
  destruct (f x') eqn:Hfx'; try discriminate.
  simpl in Hft.
  rewrite IHl; simpl; trivial.
  rewrite Bool.orb_comm, IHr; simpl; trivial.
  destruct (eqb x x') eqn:Hxx'; trivial.
  apply eqb_eq in Hxx'.
  rewrite Hxx', Hfx' in Hfx.
  discriminate.
Qed.
(* /ADMITTED *)

Lemma member_prune_right :
  forall x y t,
    comp y x = Lt ->
    all (ltb x) t = true ->
    occurs y t = false.
Proof.
(* ADMITTED *)
  intros x y t H.
  apply none_occurs.
  unfold ltb. rewrite comp_opp. rewrite H. reflexivity.
Qed.
(* /ADMITTED *)

Lemma member_prune_left :
  forall x y t,
    comp y x = Gt ->
    all (fun z => ltb z x) t = true ->
    occurs y t = false.
Proof.
(* ADMITTED *)
  intros x y t H.
  apply none_occurs.
  unfold ltb. rewrite H. reflexivity.
Qed.
(* /ADMITTED *)

(** [] *)

(** With these results, we are ready to prove the correctness of
    [member]. Notice that we state the lemma in a slightly different
    form, using an [if] expression instead of an implication
    ([->]). This allows the Coq simplification engine to perform a few
    deduction steps as we progress through the proof. *)

Lemma member_correct :
  forall x t,
    if search_tree t then member x t = occurs x t
    else True.
Proof.
  intros x t.
  induction t as [|c t1 IH1 y t2 IH2]; simpl; trivial.
  destruct (all (fun z => ltb z y) t1) eqn:H1; simpl; trivial.
  destruct (all (ltb y) t2) eqn:H2; simpl; trivial.

(** Notice how the induction hypotheses change after the following
    lines. *)

  destruct (search_tree t1) eqn:H3; simpl; trivial.
  destruct (search_tree t2) eqn:H4; simpl; trivial.
  unfold eqb. rewrite IH1, IH2.

(** Note that we can apply lemmas with universally quantified
    variables and hypotheses as functions. This has the effect of
    instantiating these quantified variables and providing proofs for
    the required hypotheses directly. *)
(** FULL: Cf. the use of [member_prune_left] and [member_prune_right]
    below. *)

(* WORKINCLASS *)
  destruct (comp x y) eqn:Hxy.
  - rewrite Bool.orb_true_r. reflexivity.
  - rewrite (member_prune_right y x t2 Hxy H2).
    rewrite Bool.orb_false_r. rewrite Bool.orb_false_r. reflexivity.
  - rewrite (member_prune_left y x t1 Hxy H1). reflexivity.
Qed.
(* /WORKINCLASS *)


(** ** The Invariant

    We now turn our attention to the actual red-black invariant. A
    red-black tree is _valid_ if (1) all paths from the root of the
    tree to its leaves go through the same number of black nodes, and
    (2) if red nodes only have black children (we stipulate that the
    leaves of the tree are black). *)
(** FULL: The [well_colored] function below checks whether (2) holds
    or not. To check (1), we use the [black_height] function defined
    below: [black_height n t] returns [true] if and only if every path
    from the root of the tree to a leaf goes through exactly [n] black
    nodes. *)

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

Fixpoint black_height n (t : tree) : bool :=
  match t, n with
  | Leaf, 0 => true
  | Node Red tl _ tr, _ =>
    black_height n tl && black_height n tr
  | Node Black tl _ tr, S n =>
    black_height n tl && black_height n tr
  | _, _ => false
  end.

(** FULL: We combine both invariants in a single [is_red_black]
    function: *)

Definition is_red_black n (t : tree) : bool :=
  well_colored t && black_height n t.

(** The red-black invariant implies that the height of the tree is
    logarithmic on the number of nodes. To prove that this is the
    case, we define a [size] function for computing various measures
    on trees. Notice that [size] takes a function argument, which
    determines which measure [size] actually computes. We can see that
    [size max] computes the height of the tree, [size min] computes
    the size of the smallest path from the root to a leaf, and [size
    plus] computes the total number of elements stored on the tree. *)

Fixpoint size (f : nat -> nat -> nat) (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ t1 _ t2 => S (f (size f t1) (size f t2))
  end.

(** It seems natural to claim that the black height of a tree is at
    most the size of its minimal path. Showing this result is
    easy. Here, we use the order relation on naturals provided by the
    standard library. *)

Lemma size_min_black_height :
  forall t n,
    if black_height n t then n <= size min t
    else True.
Proof.
  intros t.
  induction t as [|[] tl IHl x tr IHr]; intros n; simpl.
  - destruct n as [|n]; trivial.

(** Many of the results we will encounter involve integer
    inequalities. To solve these goals, we can use the [lia] tactic.

    New Tactics
    -----------

    - [lia]: Short for "Linear Integer Arithmetic"; tries to solve
      goals that involve linear systems of inequalites on integers.

    - [specialize]: Instantiate a universally quantified hypothesis *)

  - specialize (IHl n). specialize (IHr n).
    destruct (black_height n tl); trivial. simpl.
    destruct (black_height n tr); trivial. lia.

(* WORKINCLASS *)
  - destruct n as [|n]; trivial.
    specialize (IHl n). specialize (IHr n).
    destruct (black_height n tl); trivial. simpl.
    destruct (black_height n tr); trivial. lia.
Qed.
(* /WORKINCLASS *)

(** We also need to relate the black and maximal heights of a
    tree. Unlike the preceeding lemma, however, this result requires a
    clever generalization to allow the induction to go through. *)

(* EX2 (size_max_black_height) *)

(** The last part of the following proof covers trees with black
    roots, and is very similar to the analogous one for red
    roots. Your job is to complete it. *)

Lemma size_max_black_height :
  forall t n,
    if is_red_black n t then
      match tree_color t with
      | Red => size max t <= 2 * n + 1
      | Black => size max t <= 2 * n
      end
    else True.
Proof.
  intros t. unfold is_red_black.
  induction t as [|[] tl IHl x tr IHr]; simpl; intros n.
  - (* t is a Leaf *)
    destruct n; trivial.
  - (* t has a red root *)
    destruct (tree_color tl); simpl; trivial.
    destruct (tree_color tr); simpl; trivial.
    specialize (IHl n). specialize (IHr n).
    destruct (well_colored tl); simpl in *; trivial.
    destruct (well_colored tr); simpl in *; trivial.
    destruct (black_height n tl); simpl in *; trivial.
    destruct (black_height n tr); simpl in *; trivial.
    lia.
  - (* t has a black root *)
    (* ADMIT *)
    destruct (well_colored tl); simpl in *; trivial.
    destruct (well_colored tr); simpl in *; trivial.
    destruct n as [|n]; simpl in *; trivial.
    specialize (IHl n). specialize (IHr n).
    destruct (black_height n tl); simpl in *; trivial.
    destruct (black_height n tr); simpl in *; trivial.
    destruct (tree_color tl); destruct (tree_color tr); lia.
    (* /ADMIT *)
Qed.

(** [] *)

(* EX3 (size_max_size_min) *)

(** The previous two results imply the next one, which relates the
    height of the tree to the length of its mininal path. The [assert]
    tactic is used below to bring those results into the context as
    explicit hypotheses. Finish the proof. *)

Lemma size_max_size_min :
  forall t n,
    if is_red_black n t then size max t <= 2 * size min t + 1
    else True.
Proof.
  intros t n.
  assert (H1 := size_min_black_height t n).
  assert (H2 := size_max_black_height t n).
  unfold is_red_black in *.
(* ADMITTED *)
  destruct (well_colored t); simpl in *; trivial.
  destruct (black_height n t); simpl in *; trivial.
  destruct (tree_color t); simpl in *; lia.
Qed.
(* /ADMITTED *)

(** [] *)

(** Finally, we derive the bound we sought by appealing to the
    following lemma, proved using results from Coq's standard
    library.

    New Tactics
    -----------

    - [assert]: Introduce a new hypothesis in the context, requiring
      us to prove that it holds. The curly braces [{}] allow us to
      focus on the current subgoal, like [+] and [-]. *)

Lemma size_min_size_plus :
  forall t,
    size min t <= log2 (size plus t + 1).
Proof.
  intros t. apply Nat.log2_le_pow2; try lia.
  induction t as [|c t1 IH1 x t2 IH2]; simpl; trivial.
  assert (H1 : 2 ^ min (size min t1) (size min t2)
               <= 2 ^ size min t1).
  { apply Nat.pow_le_mono_r; lia. }
  assert (H2 : 2 ^ min (size min t1) (size min t2)
               <= 2 ^ size min t2).
  { apply Nat.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma is_red_black_balanced :
  forall t n,
    is_red_black n t = true ->
    size max t <= 2 * log2 (size plus t + 1) + 1.
Proof.
  intros t n H.
  assert (H1 := size_max_size_min t n). rewrite H in H1.
  assert (H2 := size_min_size_plus t). lia.
Qed.

(** ** Insertion

    Knowing that red-black trees are balanced would be useless if that
    invariant were not preserved by tree operations. To conclude this
    module, we define an insertion operation and show that it
    preserves the red-black invariant.

    Our definition is adapted from Chris Okasaki's classical paper
    "Red-Black Trees in a Functional Setting". It is essentially a
    standard insertion function on binary trees, except for an
    additional balancing step for restoring the tree invariants. *)

Definition balance_black_left tl x tr : tree :=
  match tl, x, tr with
  | Node Red (Node Red t1 x1 t2) x2 t3, x3, t4
  | Node Red t1 x1 (Node Red t2 x2 t3), x3, t4 =>
    Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4)
  | _, _, _ => Node Black tl x tr
  end.

Definition balance_black_right tl x tr : tree :=
  match tl, x, tr with
  | t1, x1, Node Red (Node Red t2 x2 t3) x3 t4
  | t1, x1, Node Red t2 x2 (Node Red t3 x3 t4) =>
    Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4)
  | _, _, _ => Node Black tl x tr
  end.

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

(** FULL: The next lemmas are not strictly necessary, but they greatly
    help us reasoning about the behavior of the balancing functions
    above. Although they rely on a feature that we're not discussing
    here in detail -- namely, _inductive propositions_ --, their use
    is relatively simple, and is illustrated in the proof of the
    [black_height_balance_left] lemma below. *)
(** TERSE: The next lemmas help us reasoning about the balancing
    functions. We won't discuss their definition in detail, but using
    them is simple -- check the [black_height_balance_left] lemma below. *)

Inductive balance_left_spec : color -> tree -> A -> tree -> tree -> Prop :=
| BalanceLeftSpec1 :
    forall t1 x1 t2 x2 t3 x3 t4,
      balance_left_spec Black (Node Red (Node Red t1 x1 t2) x2 t3) x3 t4
                        (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
| BalanceLeftSpec2 :
    forall t1 x1 t2 x2 t3 x3 t4,
      balance_left_spec Black (Node Red t1 x1 (Node Red t2 x2 t3)) x3 t4
                        (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
| BalanceLeftSpec3 :
    forall c t1 x t2,
      balance_left_spec c t1 x t2 (Node c t1 x t2).

Lemma case_balance_left :
  forall c t1 x t2,
    balance_left_spec c t1 x t2 (balance_left c t1 x t2).
Proof.
  intros [] t1 x t2; simpl; try constructor.
  destruct t1 as [|[] [|[]] ? [|[]]]; simpl; constructor.
Qed.

Inductive balance_right_spec : color -> tree -> A -> tree -> tree -> Prop :=
| BalanceRightSpec1 :
    forall t1 x1 t2 x2 t3 x3 t4,
      balance_right_spec Black t1 x1 (Node Red (Node Red t2 x2 t3) x3 t4)
                         (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
| BalanceRightSpec2 :
    forall t1 x1 t2 x2 t3 x3 t4,
      balance_right_spec Black t1 x1 (Node Red t2 x2 (Node Red t3 x3 t4))
                         (Node Red (Node Black t1 x1 t2) x2 (Node Black t3 x3 t4))
| BalanceRightSpec3 :
    forall c t1 x t2,
      balance_right_spec c t1 x t2 (Node c t1 x t2).

Lemma case_balance_right :
  forall c t1 x t2,
    balance_right_spec c t1 x t2 (balance_right c t1 x t2).
Proof.
  intros [] t1 x t2; simpl; try constructor.
  destruct t2 as [|[] [|[]] ? [|[]]]; simpl; constructor.
Qed.

Lemma black_height_balance_left :
  forall c t1 x t2 n,
    black_height n (balance_left c t1 x t2)
    = black_height n (Node c t1 x t2).
Proof.
  intros c t1 x t2 n.
  destruct (case_balance_left c t1 x t2)
    as [t1 x1 t2 x2 t3 x3 t4|t1 x1 t2 x2 t3 x3 t4|c t1 x t2]; simpl; trivial.
  - destruct n as [|n]; trivial.
    rewrite Bool.andb_assoc. reflexivity.
  - destruct n as [|n]; trivial.
    rewrite Bool.andb_assoc, Bool.andb_assoc.
    reflexivity.
Qed.

(* EX2 (black_height_balance_right) *)

(** Using the previous lemma as a template, complete the proof of
    [black_height_balance_right] below. *)

Lemma black_height_balance_right :
  forall c t1 x t2 n,
    black_height n (balance_right c t1 x t2)
    = black_height n (Node c t1 x t2).
Proof.
(* ADMITTED *)
  intros c t1 x t2 n.
  destruct (case_balance_right c t1 x t2)
    as [t1 x1 t2 x2 t3 x3 t4|t1 x1 t2 x2 t3 x3 t4|c t1 x t2]; simpl; trivial.
  - destruct n as [|n]; trivial.
    rewrite Bool.andb_assoc, Bool.andb_assoc, Bool.andb_assoc. reflexivity.
  - destruct n as [|n]; trivial.
    rewrite Bool.andb_assoc, Bool.andb_assoc, Bool.andb_assoc. reflexivity.
Qed.
(* /ADMITTED *)

(** [] *)

(* EX3 (height_ok_insert_aux) *)

(** Use the last two results to show that the black height invariant
    is preserved by [insert_aux]. *)

Lemma height_ok_insert_aux :
  forall x t n,
    black_height n (insert_aux x t)
    = black_height n t.
Proof.
(* ADMITTED *)
  intros x t.
  induction t as [|c tl IHl x' tr IHr]; intros n.
  - simpl. destruct n; trivial.
  - simpl. destruct (comp x x'); trivial.
    + rewrite black_height_balance_left. simpl.
      rewrite IHl. destruct c; trivial.
      destruct n as [|n]; trivial.
      rewrite IHl. trivial.
    + rewrite black_height_balance_right. simpl.
      rewrite IHr. destruct c; trivial.
      destruct n as [|n]; trivial.
      rewrite IHr. trivial.
Qed.
(* /ADMITTED *)

(** [] *)

(** To complete the invariant preservation proof, we must still
    analyze the effect of [insert] on the colors of a tree. This is
    not as simple as it might seem: when called on a well-colored
    tree, [insert_aux] might generate a tree that violates the
    coloring invariants at its root -- that is, the root might be red
    and also have a red child. The correct inductive generalization is
    that inserting on a red node results in a tree that is _almost_
    well-colored: *)

Definition almost_well_colored t : bool :=
  match t with
  | Leaf => true
  | Node _ t1 _ t2 => well_colored t1 && well_colored t2
  end.

(* EX1 (well_colored_weaken) *)

(** Show that well-colored trees are almost well-colored. *)

Lemma well_colored_weaken :
  forall t,
    well_colored t = true ->
    almost_well_colored t = true.
Proof.
(* ADMITTED *)
  intros t. destruct t as [|c t1 x t2]; trivial.
  simpl. rewrite <- Bool.andb_assoc, Bool.andb_comm.
  destruct (well_colored t1); trivial.
  destruct (well_colored t2); trivial.
Qed.
(* /ADMITTED *)

(** [] *)

(** The following two lemmas show that tree balancing restores the
    coloring invariant if one of the trees is almost
    well-colored. They use more advanced proof automation features to
    consider many of the cases arising in this proof at once. You
    don't have to understand how these proofs work right now, but they
    will be needed later for showing our final result. *)

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
          end); simpl; try reflexivity;
  repeat match goal with
  | |- context[match ?b with _ => _ end] =>
    destruct b; simpl; try discriminate
  | |- context[?b && _ = true] =>
    destruct b; simpl; try discriminate
  | |- _ = true -> _ =>
    intros H; rewrite H
  end; reflexivity.
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
          end); simpl; try reflexivity;
  repeat match goal with
  | |- ?b = true -> _ =>
    match b with
    | context[tree_color ?t] =>
      destruct (tree_color t); simpl; try discriminate
    | context[well_colored ?t] =>
      destruct (well_colored t); simpl; try discriminate
    end
  end; repeat rewrite Bool.andb_true_r; reflexivity.
Qed.

(* EX3 (well_colored_insert_aux) *)

(** The following lemma is the main inductive invariant required to
    show the correctess of [insert]. Complete the proof of the
    case that covers black nodes. *)

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
  - (* t is a Leaf *)
    reflexivity.
  - (* t has a Red root *)
    destruct (tree_color t1); simpl; trivial.
    destruct (tree_color t2); simpl; trivial.
    destruct (comp x x'); simpl.
    + destruct (well_colored t1 && well_colored t2); trivial.
    + destruct (well_colored t1); simpl; trivial.
      destruct (well_colored t2); simpl; trivial.
      rewrite IH1. reflexivity.
    + destruct (well_colored t1); simpl; trivial.
  - (* t has a Black root *)
    (* ADMIT *)
    destruct (comp x x'); simpl.
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
    (* /ADMIT *)
Qed.

(** [] *)

(** We can now prove our final result. The [new_black_height] function
    below computes the black height of a tree after the insertion. *)

Definition new_black_height n c :=
  match c with
  | Red => S n
  | Black => n
  end.

Lemma black_height_make_black :
  forall t n,
    black_height (new_black_height n (tree_color t)) (make_black t)
    = black_height n t.
Proof. intros [|[] t1 x t2]; reflexivity. Qed.

Lemma almost_well_colored_make_black :
  forall t, well_colored (make_black t) = almost_well_colored t.
Proof. intros [|c t1 x t2]; reflexivity. Qed.

Lemma is_red_black_insert :
  forall x n t,
    if is_red_black n t then
      is_red_black (new_black_height n (tree_color (insert_aux x t))) (insert x t) = true
    else True.
Proof.
  intros x n t.
  unfold insert, is_red_black.
  assert (H1 := well_colored_insert_aux x t).
  assert (H2 := height_ok_insert_aux x t).
  rewrite black_height_make_black.
  rewrite H2.
  rewrite almost_well_colored_make_black.
  destruct (well_colored t); simpl; trivial.
  destruct (tree_color t).
  - rewrite H1. destruct (black_height n t); trivial.
  - rewrite well_colored_weaken; trivial.
    destruct (black_height n t); trivial.
Qed.

End RedBlack.
