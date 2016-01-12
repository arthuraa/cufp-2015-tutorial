(* ###################################################################### *)

(* We will use the following option to make use of polymorphism
   more convenient. *)

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
  match l1 with
  | nil => l2
  | cons h t  => cons h (app t l2)
  end.

(** Coq comes with a syntax extension mechanism for defining custom
    notations. Without getting into details, here's how we can give
    familiar syntax for lists. *)

Notation "h :: t" := (cons h t) (at level 60, right associativity).
Notation "[ ]" := (nil _).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y [] ) ..).
Notation "l1 ++ l2" := (app l1 l2) (at level 60, right associativity).

(** Since nil can potentially be of any type, we add an underscore to tell Coq
    to infer the type from the context. *) 

(* We can now check the types of expressions involving lists. *)

Check [].
Check true :: [].
Check [true ; false]. 
Check [true ; false] ++ [false].

(* And compute the last *)
Compute [true ; false] ++ [false].


(* Note that we can define functions using notations *)

Reserved Notation "l1 @ l2" (at level 60).
Fixpoint app' T (l1 l2 : list T) : list T :=
  match l1 with
  | [] => l2
  | h :: t  => h :: (t @ l2)
  end

  where "l1 @ l2" := (app' l1 l2).


(* Exercise: Define "snoc", which adds an element to the end of a list. *)

Fixpoint snoc {T} (l : list T) (x : T) : list T :=
  [] (* Fill in here *).

(** It is easy to show that appending nil to the left of a list yields the
    original list.  *)

Lemma app_nil_l: forall T (l : list T), [] ++ l  = l.
Proof.
  intros T l.
  simpl.
  reflexivity.
Qed.

(** Showing the symmetric result is more difficult
    since it doesn't follow by simplification alone. *)

Lemma app_nil_r: forall T (l : list T), l ++ []  = l.
Proof.
  intros T l.
  simpl. (* Does nothing *)
  destruct l as [| h t]. (* Notice the [as] clause, which allows us
                            to name constructor arguments. *)
  + simpl.
    reflexivity.
  + simpl. (* no way to proceed... *)

(** The problem is that we can only prove the result for [h::t] if we
    already know that it is valid for [t]. We need a bigger hammer here...


    New tactic
    ----------

    - [induction]: Argue by induction. It works as [destruct], but
    additionally giving us an inductive hypothesis in the inductive
    case. *)

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

(** As a rule of thumb, when proving some property of a recursive
    function, it is a good idea to do induction on the recursive
    argument of the function. For instance, let's show that [app] is
    associative: *)

Lemma app_assoc :
  forall T (l1 l2 l3 : list T),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
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

(** Take-home exericse: Try to do induction on [l2] and [l3] in the
    above proof, and see where it fails. *)

(* 30 seconds *)
(* Exercise: Prove that [snoc l x] is equivalent to 
   appending [x] to the end of [l]. *)

Lemma snoc_app : forall T (l : list T) (x : T), snoc l x = l ++ [x].
Proof.
  (* Fill in here *)
Admitted.


(* Let's define the length function *)

Fixpoint length T (l : list T) :=
  match l with
  | [] => 0
  | h :: t => 1 + length t  
  end.

Compute (fun n => 1 + n).
Compute length [1; 1; 1].

(* 90 seconds *)
(* Exercise *)

Lemma app_length : forall T (l1 l2 : list T),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros T l1 l2.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.
    reflexivity.
Qed.


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

    Let's try to prove that if [l1 ++ l2 = nil] then [l1] is [nil] 

 *)

Lemma plus_nil_l : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l1 = [].
Proof.
  intros T l1 l2 H.
  destruct l1 as [| h t].
  + (* [] *)
    reflexivity.
  + (* h :: t *)  
    simpl in H.
    discriminate.
Qed.
    

(* Exercise: Prove the same about l2. *)

Lemma plus_nil_r : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l2 = [].
Proof.
  intros T l1 l2 H.
  destruct l1 as [| h t].
  + (* [] *)
    simpl in H.
    apply H.
  + (* h :: t *)  
    simpl in H.
    discriminate.
Qed.

(* Other approaches *)

Lemma plus_nil_r' : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l2 = [].
Proof.
  intros T l1 l2 H.
  destruct l2 as [| h t].
  + (* [] *)
    reflexivity.
  + (* h :: t *)  
    destruct l1; simpl in H; discriminate.
Qed.

Lemma plus_nil_r_trick : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l2 = [].
Proof.
  intros T l1 l2 H.
  assert (H1 : l1 = []).
    apply (plus_nil_l l1 l2).
    apply H.
  rewrite H1 in H.
  simpl in H.
  apply H.
Qed.



(** Let's define list reversal function and prove some of its
    basic properties. *)
 
Fixpoint rev T (l : list T) :=
  match l with
  | [] => []
  | h :: t => (rev t) ++ [h]
  end.

Lemma rev_app : forall T (l1 l2 : list T), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
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

(* Using rev_app prove that reversing a list twice results in the same list. *)

Lemma rev_involutive : forall T (l : list T), rev (rev l) = l. 
Proof.
Admitted. (* fill in proof *)




(** Notice that the definition of list reversal given above runs 
    in quadratic time. *)

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

