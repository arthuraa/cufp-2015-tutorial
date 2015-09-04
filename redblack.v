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
    avoiding having to redeclare these arguments in all
    definitions. The [Variable] and [Hypothesis] keywords introduce
    assumptions in our context that are in scope in the entire
    [Section] declaration.

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
Hypothesis comp_trans :
  forall x y z, comp x y = Lt ->
                comp y z = Lt ->
                comp x z = Lt.

(** [A <-> B] ("A if and only if B") states that [A] and [B] are
    _logically equivalent_, i.e., that [A] implies [B] and [B] implies
    [A]. It can be applied in either direction with the [apply]
    tactic. It can also be rewritten with [rewrite]. *)

Hypothesis comp_refl_iff :
  forall x y, comp x y = Eq <-> x = y.

(* Exercise: *)
Lemma comp_refl : forall x, comp x x = Eq.
Proof. Admitted.

(** Red-black trees are binary search trees that contain elements of
    [A] on their internal nodes, and such that every internal node is
    colored with either [Red] or [Black]. *)

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
    its left, and strictly smaller than those to its right. We use an
    auxiliary function [ltb] that tests whether an element [x : A] is
    smaller than some [y : A] with the [comp] function. *)

Definition ltb x y :=
  match comp x y with
  | Lt => true
  | _ => false
  end.

(** The invariant is then expressed with a simple recursive function
    that combines [all] and [ltb] above. *)

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
    [occurs] that looks for an element [x] on all nodes of a tree
    [t]. The [eqb] function, as its name suggests, tests two elements
    for equality. *)

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

(** Often, [destruct] generates many easy subgoals that can be readily
    solved. To make this more convenient, we can use the [;] tactic
    operator. An expression such as [foo; bar] first calls [foo], then
    calls [bar] on all generated subgoals. A common idiom is [foo;
    trivial], which solves the trivial subgoals and does nothing on
    the remaining ones.


    New Tactics
    -----------

    - [try]: Calling [try foo] tries to execute [foo], doing nothing
      if [foo] raises any errors. In particular, if [foo] is a
      _terminating tactic_ such as [discriminate], [try foo] attempts
      to solve the goal, and does nothing if it fails.

    - [destruct ... eqn: ...]: Do case analysis on an expression while
      generating an equation. *)

    destruct (all f t1) eqn:H1; try discriminate.
    destruct (f x) eqn:H2; try discriminate.
    destruct (all f t1) eqn:H3; try discriminate.
    rewrite IH1; trivial.
    rewrite Hfg; trivial.
    rewrite IH2; trivial.
Qed.

(* Exercise: *)
Lemma none_occurs :
  forall (x : A) (f : A -> bool) (t : tree),
    f x = false ->
    all f t = true ->
    occurs x t = false.
Proof. (* fill in here *) Admitted.

(** With these results, we are ready to prove the correctness of the
    membership testing algorithm. *)

Lemma member_correct :
  forall x t,
    search_tree t = true ->
    member x t = occurs x t.
Proof.
  intros x t.
  induction t as [|c t1 IH1 y t2 IH2]; simpl; trivial.
  intros H.
  destruct (all (fun z => ltb z y) t1) eqn:H1; try discriminate.
  destruct (all (ltb y) t2) eqn:H2; try discriminate.
  destruct (search_tree t1) eqn:H3; try discriminate.
  destruct (search_tree t2) eqn:H4; try discriminate.
  unfold eqb.
  rewrite IH1; trivial.
  rewrite IH2; trivial.

(** We often want to introduce new facts in our context. This can be
    done with the [assert] tactic.

    New Tactics
    -----------

    - [assert]: Introduce a new hypothesis in the context, requiring
      us to prove that it holds. *)

  assert (Hx : ltb x x = false).
  { unfold ltb. rewrite comp_refl. reflexivity. }

(** The curly braces [{}] allow us to focus on the current subgoal,
    like [+] and [-]. *)

  destruct (comp x y) eqn:Hxy.
  - rewrite Bool.orb_true_r. reflexivity.
  - assert (H2' : all (ltb x) t2 = true).
    { apply (all_weaken (ltb y) (ltb x)); trivial.
      intros z.
      unfold ltb.
      destruct (comp y z) eqn:Hyz; try congruence.
      rewrite (comp_trans x y z); trivial. }
    rewrite (none_occurs x (ltb x) t2 Hx H2').
    destruct (occurs x t1); reflexivity.
  - assert (Hxy' : comp y x = Lt).
    { rewrite comp_opp, Hxy. reflexivity. }
    assert (H1' : all (fun z => ltb z x) t1 = true).
    { apply (all_weaken (fun z => ltb z y) (fun z => ltb z x)); trivial.
      intros z.
      unfold ltb.
      destruct (comp z y) eqn:Hyz; try congruence.
      rewrite (comp_trans z y x); trivial. }
    rewrite (none_occurs x (fun z => ltb z x) t1); trivial.
Qed.

(** We now turn our attention to the red-black invariant. A red-black
    tree is _valid_ if (1) all paths from the root of the tree to its
    leaves go through the same number of black nodes, and (2) if red
    nodes only have black children (we stipulate that the leaves of
    the tree are black). We begin by formalizing (2). *)

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

(** The [black_height] function computes the number of black nodes on
    the path to the left-most leaf of the tree. It is used in the
    [height_ok] function, which ensures that _all_ paths have the same
    number of black nodes. *)

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

(** The red-black invariant is important because it implies that the
    height of the tree is logarithmic on the number of nodes. We will
    now see how to formally show that this is the case. We begin by
    defining a function [size] for computing various metrics about our
    trees: *)

Fixpoint size (f : nat -> nat -> nat) (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ t1 _ t2 => S (f (size f t1) (size f t2))
  end.

(** Note that [size plus] computes the number of elements stored in
    the tree. [size max] computes the height of the tree, whereas
    [size min] computes the length of the shortest path from the root
    of the tree to a leaf.

    As a warm-up exercise, let's show that the black height of a tree
    is a lower bound on the length of its minimal path: *)

Lemma size_min_black_height :
  forall t,
    if height_ok t then black_height t <= size min t
    else True.
Proof.
  intros t.
  induction t as [|c t1 IH1 x t2 IH2].

  + simpl.

(** To facilitate low-level arithmetic reasoning, we can use the [lia]
    tactic.

    New Tactics
    -----------

    - [lia]: Short for "Linear Integer Arithmetic"; tries to solve
      goals that involve linear systems of inequalites on integers. *)

  lia.

  + simpl.
    destruct (beq_nat (black_height t1) (black_height t2)) eqn:e12; simpl; trivial.
    rewrite beq_nat_true_iff in e12.
    destruct (height_ok t1); simpl; trivial.
    destruct (height_ok t2); simpl; trivial.
    destruct c; lia.
Qed.

(** We now need to relate the black height of a tree to its total
    height, by proving the following fact: *)

Lemma size_max_black_height :
  forall t,
    if is_red_black t then size max t <= 2 * black_height t + 1
    else True.
Proof. (* stuck ... *) Abort.

(** Unfortunately, this won't work. We need to reason about the
    coloring properties of red-black trees, and show the following
    slightly stronger statement, which gives an improved bound for
    black trees. *)

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
    + admit. (* fill in here *)
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

(** Exercise: Prove the following result using the previous two lemmas
    relating the height of the tree to the length of its mininal
    path. *)

Lemma size_max_size_min :
  forall t,
    if is_red_black t then size max t <= 2 * size min t + 1
    else True.
Proof. (* fill in here *) Admitted.

(** The previous lemma implies that the tree is well-balanced thanks
    to the following fact, which shows that the number of elements
    stored in a tree is exponential in the length of the minimal path:
    *)

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

(** As an interesting verification example, we will show how to verify
    that red-black-tree insertion preserves the data-structure
    invariants. This definition is taken from Okasaki's classical
    "Red-Black Trees in a Functional Setting" paper.

    The insertion algorithm works basically as regular binary-tree
    insertion, except for an additional balancing step, which is
    required to restore the tree invariants. *)

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

(** One problem with our definitions of [balance_left] and
    [balance_right] is that they are stated in terms of complicated
    patterns. Internally, these functions are ellaborated in terms of
    nested matches, which make them more complicated to reason about
    directly with [destruct]. To remedy this, we show the following
    lemmas, which allow us to consider the interesting cases directly:
    *)

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

(** This lemma shows that the black height of a tree is preserved by a
    balancing step on the left: *)

Lemma black_height_balance_left :
  forall c t1 x t2,
    black_height (balance_left c t1 x t2)
    = black_height (Node c t1 x t2).
Proof.
  intros [] t1 x t2; trivial; simpl.
  rewrite case_balance_black_left; reflexivity.
Qed.

(* Exercise: Prove this similar statement for the symmetric case. *)
Lemma black_height_balance_right :
  forall c t1 x t2,
    black_height (balance_right c t1 x t2)
    = black_height (Node c t1 x t2).
Proof. Admitted.

(* Exercise: Prove the following two lemmas, which show that the
   consistency of the black heights of a tree is preserved after a
   balancing step. You can use the [case_balance_black_left] and
   [case_balance_black_right] to make your life easier. Hint: you will
   need to reason about the behavior of [beq_nat]. *)

Lemma height_ok_balance_left :
  forall c t1 x t2,
    height_ok (balance_left c t1 x t2)
    = height_ok (Node c t1 x t2).
Proof. Admitted.

Lemma height_ok_balance_right :
  forall c t1 x t2,
    height_ok (balance_right c t1 x t2)
    = height_ok (Node c t1 x t2).
Proof. Admitted.

(** Combining these results, we can show that the black height
    invariant is preserved by [insert_aux]. This proof is left as an
    exercise. *)

Lemma black_height_insert_aux :
  forall x t,
    black_height (insert_aux x t)
    = black_height t.
Proof. Admitted.

Lemma height_ok_insert_aux :
  forall x t,
    height_ok (insert_aux x t)
    = height_ok t.
Proof. Admitted.

(** The most complicated part of the invariant preservation proof for
    the insertion algorithm is showing that nodes are still colored
    correctly after an insertion step. One problem is that, even after
    a balancing step, [insert_aux] may produce a tree that is colored
    incorrectly at its root. We formalize this property with the
    following definition: *)

Definition almost_well_colored t : bool :=
  match t with
  | Leaf => true
  | Node _ t1 _ t2 => well_colored t1 && well_colored t2
  end.

(* Exercise: Show that well-colored trees are almost well-colored. *)
Lemma well_colored_weaken :
  forall t,
    well_colored t = true ->
    almost_well_colored t = true.
Proof. Admitted.

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

Lemma height_ok_make_black :
  forall t,
    height_ok (make_black t) = height_ok t.
Proof. intros [|c t1 x t2]; reflexivity. Qed.

Lemma almost_well_colored_make_black :
  forall t, well_colored (make_black t) = almost_well_colored t.
Proof. intros [|c t1 x t2]; reflexivity. Qed.

Lemma is_red_black_insert :
  forall x t,
    if is_red_black t then is_red_black (insert x t) = true
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
