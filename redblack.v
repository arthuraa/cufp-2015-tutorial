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
