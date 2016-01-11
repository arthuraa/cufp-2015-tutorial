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
