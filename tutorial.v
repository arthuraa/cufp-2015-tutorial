(* ###################################################################### *)
(** Syntax *)

(** Everything in Coq is built from scratch -- even booleans!
    Fortunately, they are already provided by the Coq standard
    library, but we'll review their definition here to get familiar
    with the basic features of the system.

    "Inductive" is Coq's way of defining an algebraic datatype.  Its
    syntax is similar to OCaml's ([type]) or Haskell's ([data]). Here,
    we define [bool] as a simple algebraic datatype. *)

Module Bool.

Inductive bool : Type :=
  | true : bool
  | false : bool.

(* Exercise: Define a three-valued datatype, representing ternary logic.
   Here something can be true, false and unknown. *)

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

Definition andb (b1 b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


(** Let's test our functions. The [Compute] command tells Coq to
    evaluate an expression and print the result on the screen.*)

Compute (negb true).
Compute (orb true false).
Compute (andb true false).

(* Exercise: Define xor (exclusive or) . *)

Definition xorb (b1 b2 : bool) : bool :=
  true (* Change this! *).

(** What makes Coq different from normal functional programming
    languages is that it allows us to formally _prove_ that our
    programs satisfy certain properties, verifying these proofs to
    ensure that they are correct.

    We use [Lemma], [Theorem] and [Example] to write logical
    statements. Coq requires us to prove these statements using
    _tactics_, which are commands that manipulate formulas using basic
    logic rules. Here's an example: *)

(* Basic tactics: intros, simpl and reflexivity. *)

Example andb_false : forall b, andb false b = false.
Proof.
  intros b. (* introduce the variable b *)
  simpl. (* simplify the expression *)
  reflexivity. (* solve for x = x *)
Qed.

(* Basic tactics: We can use 'destruct' to do case analysis *)

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


(* Exercise: Show that false is an identity element for xor - that is,
   xor false b is equal to b *)

Theorem xorb_false: False. (* fill in claim *)
Proof.
  Admitted. (* fill in proof *)

(* NB: Admitted allows us to proceed without completing our proof. *)

(* Basic tactics : rewriting, apply *)


Theorem rewrite_example : forall b1 b2 b3 b4,
  b1 = b4 ->
  b2 = b3 ->
  andb b1 b2 = andb b3 b4.
Proof.
  intros b1 b2 b3 b4 eq14 eq23.
  rewrite eq14. (* replace b1 with b4 in the goal *)
  rewrite <- eq23. (* replace b3 with b2 in the goal. *)
  apply andb_commutative. (* solve using our earlier theorem *)
Qed.

(* Exercise: Show that if b1=b2 then xorb b1 b2 is equal to false *)

Theorem xorb_same : False. (* fill in claim *)
Proof.
  Admitted. (* fill in proof *)

End Bool.


(* Even numbers are not primitive!
   Let's define them inductively.   *)

Module Nat.

(* A natural number is either zero or the successor of a natural number *)

(* Note that bool was a simple enumeration type, where this type has a
   recursive structure. *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(* "Check" [C-c C-a C-c in Proof General, or ... in CoqIDE] allows us
   to check the type of an expression. *)

Check (S (S O)).

(* The "Fixpoint" keyword defines a recursive function *)
(* In OCaml we would use "let rec" and in Haskell no special keyword is needed. *)

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

(* Let's add some notation *)

Notation "x + y" := (plus x y) (at level 50, left associativity).

Notation "x * y" := (mult x y) (at level 40, left associativity).


(* Exercise: Define exponentiation *)

(* Fill in function here *)

(* Fill in notation here *)

(* Let's show that O is the left additive identity . *)

Lemma plus_0_l: forall n : nat, O + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(* Showing that 0 is the right additive identity is more difficult *)

(* Tactics: Induction - destructs an inductive term, giving us an inductive
   hypothesis in the inductive case. *)

Lemma plus_O_r: forall n : nat, n + O = n.
Proof.
  intros n.
  simpl. (* does nothing *)
  destruct n as [| n'].
  + simpl.
    reflexivity.
  + simpl. (* no way to proceed *)
Restart.
  intros n.
  induction n as [| n' IH]. (* Note the additional name IH, given to our
                               inductive hypothesis *)
  + simpl.
    reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
Qed.

(* Exercise: Show that n + S m is equal to S (n + m). *)

(* Let's show that plus is associative. *)

Theorem plus_assoc: forall m n o, m + (n + o) = (m + n) + o.
Proof.
  intros m n o.
  induction m as [| m' IH]. (* m is the right choice here, since plus is defined
                               by recursion on the first argument. *)
  + simpl.
    reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
Qed.

(* Exercise: Show that plus is commutative. *)
(* Hint: Look at our earlier lemmas. *)


(* Additional take-home exercises: Show that mult has an identity (S O), a
   annihilator O and associative, commutative and distributive properties. *)

Fixpoint minus (m n : nat) : nat :=
  match m, n with
    | O, _ => m
    | _, O => m
    | S m', S n' => minus m' n'
  end.

Notation "x - y" := (minus x y) (at level 50, left associativity).

Fixpoint ble_nat (m n : nat) : bool :=
  match m, n with
  | O, _ => true
  | _, O => false
  | S n', S m' => ble_nat n' m'
  end.

Fixpoint div2 (n : nat) :=
  match n with
  | O => O
  | S O => O
  | S (S n') => S (div2 n')
  end.

Fail Fixpoint div (m n: nat) {struct m} : nat :=
  match n with
  | O => O
  | S n' => if ble_nat n m then S (div (m - n) n) else O
  end.

(* This, on the other hand, words: *)

Fixpoint div (m n: nat) {struct m} : nat :=
  match n with
    | O => O
    | S n' => match m with
                | O => O
                | S m' => S (div (S m' - S n') (S n'))
              end
  end.

(* However, changing the definition of minus to equivalent ones causes
   it to break (try it!) *)

End Nat.


(* Nat is defined in Coq's standard libraries which treats 3 as syntactic sugar
   for S (S (S O)). *)

Compute (S (S O)).
Compute (S (S O) + S O).

Module List.

(* Here's a polymorphic definition: *)

Inductive list (T : Type) :=
| nil : list T
| cons : T -> list T -> list T.

(* In Coq, polymorphism is _explicit_, i.e. we need to supply type arguments. *)

Definition singleton_list (T : Type) (x : T) :=
  cons T x (nil T).

(* However, we can avoid giving arguments when Coq has enough
   information to figure them out *)

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

(* Calling "induction" on a list gives an inductive hypothesis about
   the tail of the list. *)

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

(* Lists, of course, are also defined in the standard library *)

Require Import Coq.Lists.List.
Import ListNotations.

(* Notice that the definition of rev (list reversal) given in the
standard library runs in quadratic time. *)

Print rev.

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
    SearchAbout (_ ++ _ ++ _). (* C-c C-a C-a in Proof General *)
    rewrite <- app_assoc.
    simpl.
    reflexivity.
Qed.


(* Dependently Typed Programming *)

Definition stack := list.

Definition push {T} (x:T) (s : stack T) : stack T  := x :: s.

Definition pop {T} (s : stack T) : T * stack T :=
  match s with
  | h :: t => (h, t)
  | _ => ???
  end.






Rewriting

Lists (Polymorphism)

Nat-Indexed Stacks

Tactics Cheat Sheet