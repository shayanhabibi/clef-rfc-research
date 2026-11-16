From Stdlib Require Import List Bool.
Import ListNotations.
From Clef Require Import Spec.Types Spec.Runtime Spec.Witnesses.
From Clef Require Import RFC0001.Constraints RFC0001.TypeCase RFC0002.Regions.

(**md # Arm bodies and how overlapping arms are glued

[Regions](Clef.RFC0002.Regions.html) says which arm a specialization selects. This module gives
each arm a body, with typing and evaluation, and asks two questions the tests alone cannot answer.

1. Is a definition whose arm bodies check safe to run at every instantiation?
2. When two arms overlap, what must hold for the program not to depend on their order?

```fsharp
let f<'A, 'B, 'T when 'A : (int | string)
                 and 'B : (string | float)
                 and 'T : ('A | 'B)> (x: 'T) : 'T =
    match x with
    | :? 'A as a -> a      // a is used at the type 'A
    | :? 'B as b -> b      // b is used at the type 'B
```

A body is a term of [RFC 0001](Clef.RFC0001.TypeCase.html) with no type-case of its own. A
type-case nested in an arm is not modelled.
*)

(**md ## Types open in the three variables *)

(** A type that may mention the three variables. *)
Inductive oty3 : Type :=
| VA
| VB
| VT
| O3Con (c : tycon)
| O3Pair (a b : oty3).

(** The closed type an open type stands for at an instantiation.
    - [s:] the instantiation.
    - [o:] the open type. *)
Fixpoint inst3ty (s : inst3) (o : oty3) : ty :=
  match o with
  | VA => iA s
  | VB => iB s
  | VT => iT s
  | O3Con c => TCon c
  | O3Pair a b => TPair (inst3ty s a) (inst3ty s b)
  end.

(**md ## Arms with bodies

An arm is a test and a body. The body sees the scrutinee through the arm's binders, one for each
variable the test names, followed by the other parameters of the definition. The arm `:? 'A as a`
has one binder, used at the type `'A`. The arm `:? 'A & :? 'B` has two, one at each type.
*)

(** An arm: its test and its body. *)
Record arm : Type := Arm { atest : test; abody : mtm }.

(** The number of binders a test introduces. *)
Fixpoint arity (p : test) : nat :=
  match p with
  | IsA => 1
  | IsB => 1
  | Both p q => arity p + arity q
  end.

(** Whether an arm's test succeeds at an instantiation. *)
Definition amatches (r : reading) (CA CB : cset) (s : inst3) (a : arm) : bool :=
  matches r CA CB s (atest a).

(** The arm a specialization uses: the first whose test succeeds. *)
Definition selecta (r : reading) (CA CB : cset) (arms : list arm) (s : inst3) : option arm :=
  find (amatches r CA CB s) arms.

(** Selecting among arms selects the same test as selecting among their tests. *)
Lemma find_map {A B : Type} (f : B -> bool) (g : A -> B) (l : list A) :
  find f (map g l) = option_map g (find (fun a => f (g a)) l).
Proof.
  induction l as [| a l IH]; simpl; [reflexivity |].
  destruct (f (g a)); [reflexivity | exact IH].
Qed.

(** The test selected among the tests of the arms is the test of the arm selected. *)
Lemma select_atest (r : reading) (CA CB : cset) (arms : list arm) (s : inst3) :
  select r CA CB (map atest arms) s = option_map atest (selecta r CA CB arms s).
Proof.
  unfold select, selecta. rewrite find_map. reflexivity.
Qed.

(**md ## Checking a definition

The check runs over the table of instantiations. At each one, some arm must match, and the body of
every arm that matches must have the declared result type. A body is typed with each binder at the
type of the variable its test names, which is where the two readings of a test part ways.
*)

(** Whether an arm's body has the declared result type at an instantiation.
    - [G:] the types of the other parameters.
    - [res:] the declared result type. *)
Definition arm_ok (s : inst3) (G : list oty3) (res : oty3) (a : arm) : bool :=
  match mtype (binder_types s (atest a) ++ map (inst3ty s) G) (abody a) with
  | Some t => tyeqb t (inst3ty s res)
  | None => false
  end.

(** The check of a definition, as the compiler computes it at the definition. *)
Definition check3 (r : reading) (CA CB : cset) (G : list oty3) (arms : list arm) (res : oty3)
  : bool :=
  forallb
    (fun s =>
       existsb (amatches r CA CB s) arms
       && forallb (fun a => implb (amatches r CA CB s a) (arm_ok s G res a)) arms)
    (table CA CB).

(**md ## What a definition computes *)

(** The value of a definition at an instantiation: the body of the selected arm, run with the
    scrutinee bound to each of the arm's binders.
    - [env:] the values of the other parameters.
    - [x:] the scrutinee. *)
Definition run (r : reading) (CA CB : cset) (arms : list arm) (s : inst3)
  (env : list val) (x : val) : option val :=
  match selecta r CA CB arms s with
  | Some a => eval (repeat x (arity (atest a)) ++ env) (abody a)
  | None => None
  end.

(** A list that has an element passing a test has a first one. *)
Lemma existsb_find {A : Type} (f : A -> bool) (l : list A) :
  existsb f l = true -> exists a, find f l = Some a.
Proof.
  induction l as [| a l IH]; simpl; [discriminate |].
  destruct (f a); [intros _; exists a; reflexivity | exact IH].
Qed.

(** Under the equation reading, the scrutinee has the type of every binder of an arm that
    matches. *)
Lemma binders_typed (CA CB : cset) (s : inst3) (x : val) (p : test) :
  matches Equation CA CB s p = true -> has_ty x (iT s) ->
  Forall2 has_ty (repeat x (arity p)) (binder_types s p).
Proof.
  intros M H. induction p as [| | p1 IH1 p2 IH2].
  - constructor; [| constructor].
    rewrite (equation_refines CA CB s IsA M (iA s)); [exact H | simpl; auto].
  - constructor; [| constructor].
    rewrite (equation_refines CA CB s IsB M (iB s)); [exact H | simpl; auto].
  - simpl in M. apply andb_true_iff in M. destruct M as [M1 M2].
    simpl. rewrite repeat_app. apply Forall2_app; [exact (IH1 M1) | exact (IH2 M2)].
Qed.

(**md
**Under the equation reading, a definition that checks runs to a value at every instantiation.**

Take a definition whose check passes, any instantiation that satisfies the constraints, a
scrutinee of the type `'T` is instantiated to, and arguments of the parameter types. The definition
returns a value of the declared result type. The check at the definition is all that is needed.

This is RFC 0001's `checked_definition_runs` for several variables. It rests on the same
assumption, that every witness is implemented at its declared type.

- [G:] the types of the other parameters.
- [res:] the declared result type.
- [x:] the scrutinee.
*)
Theorem checked_match_runs
  (CA CB : cset) (G : list oty3) (arms : list arm) (res : oty3)
  (s : inst3) (env : list val) (x : val) :
  check3 Equation CA CB G arms res = true ->
  valid CA CB s -> has_ty x (iT s) ->
  Forall2 has_ty env (map (inst3ty s) G) ->
  exists v, run Equation CA CB arms s env x = Some v /\ has_ty v (inst3ty s res).
Proof.
  intros C V Hx HE. unfold check3 in C. rewrite forallb_forall in C.
  specialize (C s (proj2 (table_iff_valid CA CB s) V)).
  apply andb_true_iff in C. destruct C as [C1 C2].
  destruct (existsb_find _ _ C1) as [a F].
  unfold run, selecta. rewrite F.
  destruct (find_some _ _ F) as [Ia Ma].
  rewrite forallb_forall in C2. specialize (C2 a Ia). rewrite Ma in C2. simpl in C2.
  unfold arm_ok in C2.
  destruct (mtype (binder_types s (atest a) ++ map (inst3ty s) G) (abody a)) as [t |] eqn:T;
    [| discriminate].
  apply tyeqb_iff in C2. subst t.
  apply (specialization_is_safe (abody a) _ _ _ (Forall2_app (binders_typed CA CB s x _ Ma Hx) HE) T).
Qed.

(** A value has one type. *)
Lemma has_ty_fun (v : val) : forall s t : ty, has_ty v s -> has_ty v t -> s = t.
Proof.
  induction v as [c x | a IHa b IHb]; intros s t Hs Ht.
  - inversion Hs; inversion Ht; subst; reflexivity.
  - inversion Hs; inversion Ht; subst. f_equal; [apply IHa | apply IHb]; assumption.
Qed.

(**md
**Under the membership reading, a definition that checks can return a value of the wrong type.**

The claim that a checked definition returns a value of its declared type is false under the
membership reading, whenever two different types exist and one of them has a value. Take
`'A : (x | y)`, `'B : (y)` and the one-arm match `| :? 'A as a -> a` with declared result `'A`. It
passes the check. At the instantiation where `'A` is `x` and the scrutinee has type `y`, the arm
matches because `y` is a member of `'A`'s set, and the definition returns a `y` where an `x` was
declared.

This is the unsoundness `membership_refines_falsified` predicts, shown in a program that runs. The
membership reading is sound only if a binder is typed at the scrutinee's type, never at the
variable the test names.

- [x:] the type `'A` is instantiated to.
- [y:] the type of the scrutinee.
- [v:] a value of the scrutinee's type.
*)
Theorem membership_binding_falsified (x y : ty) (v : val) :
  x <> y -> has_ty v y ->
  ~ (forall (CA CB : cset) (G : list oty3) (arms : list arm) (res : oty3)
            (s : inst3) (env : list val) (xv : val),
       check3 Membership CA CB G arms res = true ->
       valid CA CB s -> has_ty xv (iT s) ->
       Forall2 has_ty env (map (inst3ty s) G) ->
       exists w, run Membership CA CB arms s env xv = Some w /\ has_ty w (inst3ty s res)).
Proof.
  intros N Hv H.
  assert (M : forall t, t = x \/ t = y -> memb t [x; y] = true).
  { intros t Ht. apply memb_iff. unfold sat. simpl. destruct Ht; auto. }
  destruct (H [x; y] [y] [] [Arm IsA (MVar 0)] VA (Inst x y y) [] v) as [w [R W]].
  - unfold check3. apply forallb_forall. intros s Hs. apply table_iff_valid in Hs.
    destruct Hs as [Ha [Hb Ht]]. unfold sat in Ha, Hb. simpl in Ha, Hb.
    assert (Mt : memb (iT s) [x; y] = true).
    { apply M. destruct Ht as [-> | ->]; intuition congruence. }
    cbn [existsb forallb]. unfold amatches, arm_ok.
    cbn [atest abody matches binder_types app map mtype nth_error].
    rewrite Mt, tyeqb_refl. reflexivity.
  - unfold valid, sat. simpl. intuition.
  - exact Hv.
  - constructor.
  - unfold run, selecta in R. cbn [find] in R. unfold amatches in R.
    cbn [atest matches iT] in R. rewrite (M y (or_intror eq_refl)) in R.
    simpl in R. injection R as <-. apply N. exact (has_ty_fun v x y W Hv).
Qed.

(**md ## Gluing overlapping arms

With bodies in the model, the claim that arm order does not matter can be stated about what the
program computes, not about which tests succeed. Two ways of making it true are compared.

- **Priority.** Where two arms overlap, one of them is strictly more specific, and it wins. This is
  the overlap check of [Regions](Clef.RFC0002.Regions.html), with one addition.
- **Agreement.** Where two arms overlap, their bodies compute the same result, so it does not
  matter which one runs.
*)

(** Two arms agree at an instantiation when their bodies return the same result for every
    scrutinee of the type `'T` is instantiated to. *)
Definition agree_at (s : inst3) (a b : arm) : Prop :=
  forall (env : list val) (v : val), has_ty v (iT s) ->
    eval (repeat v (arity (atest a)) ++ env) (abody a) =
    eval (repeat v (arity (atest b)) ++ env) (abody b).

(** One test is strictly more specific than another when it succeeds only where the other does,
    and not everywhere the other does. *)
Definition lt (r : reading) (CA CB : cset) (p q : test) : bool :=
  le r CA CB p q && negb (le r CA CB q p).

(** A list of arms glues when, at every instantiation, the selected arm is strictly more specific
    than each other arm that matches there, or agrees with it. *)
Definition glues (r : reading) (CA CB : cset) (arms : list arm) : Prop :=
  forall (s : inst3) (p q : arm),
    valid CA CB s ->
    selecta r CA CB arms s = Some p ->
    In q arms -> amatches r CA CB s q = true ->
    lt r CA CB (atest p) (atest q) = true \/ agree_at s p q.

(**md
**Arms that glue compute the same result in any order.**

Take two lists holding the same arms, both gluing. At every instantiation and for every scrutinee
of the right type, the two definitions return the same result. This is the statement about
programs that `order_is_irrelevant` makes about tests. It holds under both readings.

- [l1:] the arms in one order.
- [l2:] the same arms in another order.
*)
Theorem glued_order_irrelevant
  (r : reading) (CA CB : cset) (l1 l2 : list arm) (s : inst3) (env : list val) (x : val) :
  glues r CA CB l1 -> glues r CA CB l2 ->
  (forall a, In a l1 <-> In a l2) ->
  valid CA CB s -> has_ty x (iT s) ->
  run r CA CB l1 s env x = run r CA CB l2 s env x.
Proof.
  intros G1 G2 P V Hx. unfold run.
  destruct (selecta r CA CB l1 s) as [p1 |] eqn:F1;
    destruct (selecta r CA CB l2 s) as [p2 |] eqn:F2.
  - destruct (find_some _ _ F1) as [I1 M1]. destruct (find_some _ _ F2) as [I2 M2].
    destruct (G1 s p1 p2 V F1 (proj2 (P p2) I2) M2) as [L1 | A1].
    + destruct (G2 s p2 p1 V F2 (proj1 (P p1) I1) M1) as [L2 | A2].
      * unfold lt in L1, L2. apply andb_true_iff in L1. apply andb_true_iff in L2.
        destruct L1 as [L1 _]. destruct L2 as [_ L2]. rewrite L1 in L2. discriminate.
      * symmetry. apply A2. exact Hx.
    + apply A1. exact Hx.
  - destruct (find_some _ _ F1) as [I1 M1].
    pose proof (find_none _ _ F2 p1 (proj1 (P p1) I1)) as E. rewrite M1 in E. discriminate.
  - destruct (find_some _ _ F2) as [I2 M2].
    pose proof (find_none _ _ F1 p2 (proj2 (P p2) I2)) as E. rewrite M2 in E. discriminate.
  - reflexivity.
Qed.

(**md ### Priority *)

(** The pair `v, v` is not `v`. *)
Lemma pair_neq (v : val) : v <> VPair v v.
Proof.
  induction v as [c x | a IHa b IHb]; intro E.
  - discriminate.
  - injection E as E1 E2. apply IHa. rewrite <- E2 in E1. rewrite E1 at 1. rewrite E2 at 1.
    rewrite <- E1 at 1. congruence.
Qed.

(** A test followed by its own conjunction with itself passes the overlap check. *)
Lemma dup_ordered_1 (r : reading) (CA CB : cset) :
  ordered r CA CB [] [IsA; Both IsA IsA] = true.
Proof.
  cbn [ordered app]. apply andb_true_iff. split; [| apply andb_true_iff; split; [| reflexivity]];
    apply forallb_forall; intros s _; cbn [find].
  - destruct (matches r CA CB s IsA); reflexivity.
  - change (matches r CA CB s (Both IsA IsA))
      with (matches r CA CB s IsA && matches r CA CB s IsA).
    destruct (matches r CA CB s IsA); cbn [andb implb]; [| reflexivity].
    apply le_iff. intros s' _ M.
    change (matches r CA CB s' IsA && matches r CA CB s' IsA = true). rewrite M. reflexivity.
Qed.

(** The same two tests in the other order pass the overlap check as well. *)
Lemma dup_ordered_2 (r : reading) (CA CB : cset) :
  ordered r CA CB [] [Both IsA IsA; IsA] = true.
Proof.
  cbn [ordered app]. apply andb_true_iff. split; [| apply andb_true_iff; split; [| reflexivity]];
    apply forallb_forall; intros s _; cbn [find].
  - destruct (matches r CA CB s (Both IsA IsA)); reflexivity.
  - change (matches r CA CB s (Both IsA IsA))
      with (matches r CA CB s IsA && matches r CA CB s IsA).
    destruct (matches r CA CB s IsA); cbn [andb implb]; [| reflexivity].
    apply le_both_l.
Qed.

(**md
**The overlap check alone does not make arm order irrelevant once arms have bodies.**

The claim that two lists with the same arms, both passing the overlap check, compute the same
result is false whenever some type has a value. The arms `:? 'A` and `:? 'A & :? 'A` test the same
thing, so each is as specific as the other and the check accepts them in either order. Give them
different bodies and the order decides which runs.

`order_is_irrelevant` is not contradicted: it says the two selected tests are equally specific,
which they are. It does not say the two selected arms are the same arm.

- [z:] a type that has a value.
- [v:] a value of that type.
*)
Theorem ordered_order_irrelevant_falsified (z : ty) (v : val) :
  has_ty v z ->
  ~ (forall (r : reading) (CA CB : cset) (l1 l2 : list arm) (s : inst3)
            (env : list val) (x : val),
       ordered r CA CB [] (map atest l1) = true ->
       ordered r CA CB [] (map atest l2) = true ->
       (forall a, In a l1 <-> In a l2) ->
       valid CA CB s -> has_ty x (iT s) ->
       run r CA CB l1 s env x = run r CA CB l2 s env x).
Proof.
  intros Hv H.
  specialize (H Equation [z] [z]
                [Arm IsA (MVar 0); Arm (Both IsA IsA) (MPair (MVar 0) (MVar 0))]
                [Arm (Both IsA IsA) (MPair (MVar 0) (MVar 0)); Arm IsA (MVar 0)]
                (Inst z z z) [] v
                (dup_ordered_1 Equation [z] [z]) (dup_ordered_2 Equation [z] [z])).
  assert (E : run Equation [z] [z]
                [Arm IsA (MVar 0); Arm (Both IsA IsA) (MPair (MVar 0) (MVar 0))]
                (Inst z z z) [] v =
              run Equation [z] [z]
                [Arm (Both IsA IsA) (MPair (MVar 0) (MVar 0)); Arm IsA (MVar 0)]
                (Inst z z z) [] v).
  { apply H.
    - intro a. simpl. tauto.
    - unfold valid, sat. simpl. auto.
    - exact Hv. }
  unfold run, selecta in E. cbn [find] in E. unfold amatches in E.
  cbn [atest matches iT iA] in E. rewrite tyeqb_refl in E. simpl in E.
  injection E as E. exact (pair_neq v E).
Qed.

(**md
**The overlap check glues when no two arms test the same thing.**

Add one requirement to the overlap check: two different arms never have tests that succeed at
exactly the same instantiations. Then the selected arm is strictly more specific than every other
arm that matches, and the arms glue. The requirement is computable, since specificity is computed
over the table, and an arm that fails it can never be selected in one of the two orders.

With `glued_order_irrelevant`, this is the corrected form of the claim that arm order does not
change the program.
*)
Theorem priority_glues (r : reading) (CA CB : cset) (arms : list arm) :
  ordered r CA CB [] (map atest arms) = true ->
  (forall a b, In a arms -> In b arms ->
     le r CA CB (atest a) (atest b) = true -> le r CA CB (atest b) (atest a) = true -> a = b) ->
  glues r CA CB arms.
Proof.
  intros O D s p q V F Hq M.
  destruct (find_some _ _ F) as [Hp _].
  assert (L : le r CA CB (atest p) (atest q) = true).
  { apply (first_match_is_most_specific r CA CB (map atest arms) s (atest p) (atest q) O V).
    - rewrite select_atest, F. reflexivity.
    - apply in_map. exact Hq.
    - exact M. }
  destruct (le r CA CB (atest q) (atest p)) eqn:L2.
  - right. rewrite (D p q Hp Hq L L2). intros env v _. reflexivity.
  - left. unfold lt. rewrite L, L2. reflexivity.
Qed.

(**md ### Agreement *)

(** Two arms with one binder each and the same body glue, whatever the constraints are. *)
Lemma same_body_glues (r : reading) (CA CB : cset) (b : mtm) :
  glues r CA CB [Arm IsA b; Arm IsB b].
Proof.
  intros s p q V F Hq M. right. destruct (find_some _ _ F) as [Hp _].
  intros env v _. simpl in Hp, Hq.
  destruct Hp as [<- | [<- | []]]; destruct Hq as [<- | [<- | []]]; reflexivity.
Qed.

(**md
**Agreement accepts a match that priority rejects.**

For `'A : (x | y)` and `'B : (y)`, the two-arm match whose arms have the same body glues, so its
result does not depend on arm order. The overlap check rejects the same match, because neither arm
is more specific and no intersection arm is written. Under agreement the intersection arm is not
needed when the two bodies already say the same thing.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
- [b:] the body both arms have.
*)
Theorem agreement_accepts_what_priority_rejects (x y : ty) (b : mtm) :
  x <> y ->
  glues Equation [x; y] [y] [Arm IsA b; Arm IsB b] /\
  ordered Equation [x; y] [y] [] (map atest [Arm IsA b; Arm IsB b]) = false.
Proof.
  intro N. split.
  - apply same_body_glues.
  - exact (unordered_overlap_rejected x y N).
Qed.
