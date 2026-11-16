From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.
From Clef Require Import Spec.Types Spec.Runtime Spec.Witnesses.
From Clef Require Import RFC0001.Constraints RFC0001.TypeCase.

(**md # Laws and theorems per member

This module models an extension. It is not part of the RFC's proposal.
[Discussion](Clef.RFC0001.Discussion.html) lists it under possible extensions, and says what would
have to be decided before it could be proposed.

A closed-set constraint lists every type its variable can be. A statement about the operations of
the variable is therefore a finite list of obligations, one per member. This module models two
uses of that.

- **Laws.** A member set may carry a law, such as associativity of `+`, when the law holds at
  every member. A specialization may then be rewritten by the law.
- **Theorems.** A library theorem that derives one law from others is proved once, and applies at
  every member whose premises are discharged.

```fsharp
// The set carries associativity of (+): it holds at int and at int64.
let sum3<'T when 'T : (int | int64)> (x: 'T) (y: 'T) (z: 'T) : 'T = (x + y) + z
// A compiler may compute x + (y + z) in a specialization. It may not for (int | float).
```

Integer addition is associative and rounded floating-point addition is not. The specification
names the hazard:
[Numeric Selection §10.5.1](https://clef-lang.com/spec/draft/numeric-selection/#1051-obligations-by-arithmetic-family)
says rounded operations are not to be assumed associative, and
[§13](https://clef-lang.com/spec/draft/numeric-selection/#13-normative-requirements) says that
recognising a reduction does not authorise reassociation. A law carried by a member set is the
evidence that authorises it.

The model cannot decide whether a law holds. An operation is an assumption of the model
([Spec.Witnesses](Clef.Spec.Witnesses.html)), so a law is a statement about every value of a
member. That is the position of a compiler: a law is an obligation, discharged per member by an
analysis or a solver, which is Tier 2 work. The theorems here say what a discharged obligation
permits and when it must be discharged again.

A rewritten specialization must also still be typed. That is a second condition on a law, that
its two sides have the same type at the member. It is separate from the law holding, and it is
decided by computation. `rewritten_definition_keeps_type` is type preservation under it.
*)

(**md ## Laws

A law is an equation between two expressions built from operations. Its variables stand for values
of the constrained type.
*)

(** One side of a law. Variables are numbered from zero. *)
Inductive lterm : Type :=
| LVar (n : nat)
| LPrim (o : op) (a : lterm)
| LPair (a b : lterm).

(** A law: an equation between two sides over a number of variables, each of the constrained
    type. *)
Record law : Type := Law {
  arity : nat;
  lhs : lterm;
  rhs : lterm
}.

(** An operation applied to two arguments. Operations take one argument, so two are passed as a
    pair. *)
Definition bin (o : op) (a b : lterm) : lterm := LPrim o (LPair a b).

(** Associativity of an operation: `(x ∘ y) ∘ z = x ∘ (y ∘ z)`. *)
Definition associative (o : op) : law :=
  Law 3 (bin o (bin o (LVar 0) (LVar 1)) (LVar 2)) (bin o (LVar 0) (bin o (LVar 1) (LVar 2))).

(** Commutativity of an operation: `x ∘ y = y ∘ x`. *)
Definition commutative (o : op) : law :=
  Law 2 (bin o (LVar 0) (LVar 1)) (bin o (LVar 1) (LVar 0)).

(** The type of one side of a law, or [None] when it has none. An operation is typed by its
    witness, as in a specialization.
    - [G:] the types of the law's variables.
    - [p:] the side. *)
Fixpoint ltype (G : list ty) (p : lterm) : option ty :=
  match p with
  | LVar n => nth_error G n
  | LPrim o a =>
      match ltype G a with
      | Some s => witness o s
      | None => None
      end
  | LPair a b =>
      match ltype G a, ltype G b with
      | Some x, Some y => Some (TPair x y)
      | _, _ => None
      end
  end.

(** An implementation of the operations: what each computes on a value. The specification's
    implementation is [apply]. *)
Definition impl : Type := op -> val -> option val.

(** The value of one side of a law under an implementation.
    - [I:] the implementation of the operations.
    - [vs:] the values of the law's variables.
    - [p:] the side. *)
Fixpoint levalI (I : impl) (vs : list val) (p : lterm) : option val :=
  match p with
  | LVar n => nth_error vs n
  | LPrim o a =>
      match levalI I vs a with
      | Some v => I o v
      | None => None
      end
  | LPair a b =>
      match levalI I vs a, levalI I vs b with
      | Some x, Some y => Some (VPair x y)
      | _, _ => None
      end
  end.

(** A law holds at a type under an implementation when its two sides are equal on all values of
    that type.
    - [I:] the implementation of the operations.
    - [t:] the type the law's variables range over.
    - [l:] the law. *)
Definition holdsI (I : impl) (t : ty) (l : law) : Prop :=
  forall vs, Forall2 has_ty vs (repeat t (arity l)) ->
  levalI I vs (lhs l) = levalI I vs (rhs l).

(** A law holds at a type: it holds there under the specification's implementation. This is one
    obligation. *)
Definition holds_at (t : ty) (l : law) : Prop := holdsI apply t l.

(**md ## The laws a member set carries *)

(** A member set carries a law when the law holds at every member. *)
Definition carries (C : cset) (l : law) : Prop :=
  forall t, sat t C -> holds_at t l.

(** The obligations of a member set and a list of laws: one per member and law. *)
Definition obligations (C : cset) (L : list law) : list (ty * law) := list_prod C L.

(** There are as many obligations as members times laws. *)
Lemma obligations_count (C : cset) (L : list law) :
  length (obligations C L) = length C * length L.
Proof.
  apply length_prod.
Qed.

(**md
**The obligations of a closed set are a finite list.**

A member set carries each of a list of laws exactly when every obligation in the list holds. The
list has one entry per member and law, so the statement "the law holds at every type the variable
can be" is checked by a bounded number of checks. An open constraint has no such list.

- [C:] the member set.
- [L:] the laws.
*)
Theorem obligations_exact (C : cset) (L : list law) :
  (forall t l, In (t, l) (obligations C L) -> holds_at t l) <->
  (forall l, In l L -> carries C l).
Proof.
  unfold obligations, carries, sat. split.
  - intros H l Hl t Ht. apply H. apply in_prod_iff. split; assumption.
  - intros H t l Hin. apply in_prod_iff in Hin. destruct Hin as [Ht Hl].
    apply (H l Hl t Ht).
Qed.

(**md
**Adding a member adds its own obligations and disturbs no other.**

A set with one more member carries a law exactly when the law holds at the new member and the old
set carries it. Evidence already held for the old members stays valid. Only the new member is
checked.

- [t:] the member added.
- [C:] the member set before.
*)
Theorem carries_member (C : cset) (t : ty) (l : law) :
  carries (t :: C) l <-> holds_at t l /\ carries C l.
Proof.
  unfold carries, sat. split.
  - intros H. split.
    + apply H. left. reflexivity.
    + intros u Hu. apply H. right. exact Hu.
  - intros [Ht HC] u Hu. destruct Hu as [E | Hu].
    + subst u. exact Ht.
    + apply HC. exact Hu.
Qed.

(**md
**Evidence for a set holds for every set that entails it.**

A law carried by a member set is carried by every narrower set. This is the rule that moves
evidence to a callee's caller: no obligation is discharged again when a constrained variable is
used at a wider constraint. Removing a member never invalidates a law.

- [C:] the narrower member set.
- [D:] the member set that carries the law.
*)
Theorem law_narrowing (C D : cset) (l : law) :
  entails C D -> carries D l -> carries C l.
Proof.
  intros HE HD t Ht. apply HD. apply (proj1 (entails_iff_sat C D) HE). exact Ht.
Qed.

(**md
**An intersection carries the laws of both constraints.**

When unification intersects two member sets, the result carries every law either of them carried.
*)
Theorem meet_carries (C D : cset) (l : law) :
  carries C l \/ carries D l -> carries (meet C D) l.
Proof.
  intros [H | H] t Ht; apply meet_sat in Ht; apply H; apply Ht.
Qed.

(**md ## Rewriting a specialization by a law

A law is used by replacing an instance of one side with the same instance of the other. An
instance substitutes a specialized term for each variable of the law.
*)

(** The instance of one side of a law, or [None] when the side mentions a variable with no
    argument.
    - [s:] the argument for each variable of the law.
    - [p:] the side. *)
Fixpoint linst (s : list mtm) (p : lterm) : option mtm :=
  match p with
  | LVar n => nth_error s n
  | LPrim o a => option_map (MPrim o) (linst s a)
  | LPair a b =>
      match linst s a, linst s b with
      | Some x, Some y => Some (MPair x y)
      | _, _ => None
      end
  end.

(**md
One rewrite step, in a specialization at a given member. The step applies a law in either
direction, at the top of a term or inside it.

The side condition on a law step is that every argument has the member's type. It is needed
because one operation has a witness at several types. In a specialization at `int`, a sum of two
`float` values is still a floating-point sum, and the associativity of integer addition says
nothing about it.

- [L:] the laws that may be used.
- [t:] the member the specialization is at.
*)
Inductive rw (L : list law) (t : ty) : list ty -> mtm -> mtm -> Prop :=
| RwLaw (G : list ty) (l : law) (s : list mtm) (m m' : mtm) :
    In l L -> length s = arity l ->
    Forall (fun a => mtype G a = Some t) s ->
    linst s (lhs l) = Some m -> linst s (rhs l) = Some m' ->
    rw L t G m m'
| RwBack (G : list ty) (l : law) (s : list mtm) (m m' : mtm) :
    In l L -> length s = arity l ->
    Forall (fun a => mtype G a = Some t) s ->
    linst s (lhs l) = Some m -> linst s (rhs l) = Some m' ->
    rw L t G m' m
| RwPrim (G : list ty) (o : op) (a a' : mtm) :
    rw L t G a a' -> rw L t G (MPrim o a) (MPrim o a')
| RwPairL (G : list ty) (a a' b : mtm) :
    rw L t G a a' -> rw L t G (MPair a b) (MPair a' b)
| RwPairR (G : list ty) (a b b' : mtm) :
    rw L t G b b' -> rw L t G (MPair a b) (MPair a b')
| RwFst (G : list ty) (a a' : mtm) :
    rw L t G a a' -> rw L t G (MFst a) (MFst a')
| RwSnd (G : list ty) (a a' : mtm) :
    rw L t G a a' -> rw L t G (MSnd a) (MSnd a')
| RwLetL (G : list ty) (a a' b : mtm) :
    rw L t G a a' -> rw L t G (MLet a b) (MLet a' b)
| RwLetR (G : list ty) (a b b' : mtm) (x : ty) :
    mtype G a = Some x -> rw L t (x :: G) b b' -> rw L t G (MLet a b) (MLet a b').

(** Any number of rewrite steps. *)
Inductive rws (L : list law) (t : ty) (G : list ty) : mtm -> mtm -> Prop :=
| RwsRefl (m : mtm) : rws L t G m m
| RwsStep (m m' m'' : mtm) : rw L t G m m' -> rws L t G m' m'' -> rws L t G m m''.

(** An instance of a side evaluates to the side's value on the values of the arguments. *)
Lemma linst_eval (env : list val) (s : list mtm) (vs : list val) :
  (forall n a, nth_error s n = Some a -> eval env a = nth_error vs n) ->
  forall (p : lterm) (m : mtm), linst s p = Some m -> eval env m = levalI apply vs p.
Proof.
  intros H p. induction p as [n | o a IH | a IHa b IHb]; intros m Hm; simpl in Hm.
  - simpl. apply H. exact Hm.
  - destruct (linst s a) as [x |]; [| discriminate]. simpl in Hm. injection Hm as <-.
    simpl. rewrite (IH x eq_refl). reflexivity.
  - destruct (linst s a) as [x |]; [| discriminate].
    destruct (linst s b) as [y |]; [| discriminate].
    injection Hm as <-. simpl. rewrite (IHa x eq_refl), (IHb y eq_refl). reflexivity.
Qed.

(** Arguments that have the member's type evaluate to values of the member's type. *)
Lemma args_evaluate (G : list ty) (env : list val) (t : ty) :
  Forall2 has_ty env G ->
  forall s : list mtm, Forall (fun a => mtype G a = Some t) s ->
  exists vs, Forall2 has_ty vs (repeat t (length s)) /\
    forall n a, nth_error s n = Some a -> eval env a = nth_error vs n.
Proof.
  intros HE s Hs. induction Hs as [| a s Ha Hs IH].
  - exists []. split; [constructor |]. intros n b H. destruct n; discriminate.
  - destruct IH as [vs [Hvs Hn]].
    destruct (specialization_is_safe a G env t HE Ha) as [v [Hv Hty]].
    exists (v :: vs). split.
    + simpl. constructor; assumption.
    + intros n b H. destruct n as [| n]; simpl in *.
      * injection H as <-. exact Hv.
      * apply Hn. exact H.
Qed.

(**md
**Rewriting by a law that holds at the member does not change the result.**

Take a specialization at a member, and laws that hold at that member. A term obtained by one
rewrite step evaluates to the same result on every input of the right types, including the case
where evaluation is stuck. This rests on the assumption that every witness is implemented at its
declared type, which is what makes the arguments of a law step values of the member's type.

- [L:] the laws used.
- [t:] the member.
*)
Theorem rewrite_sound (L : list law) (t : ty) :
  (forall l, In l L -> holds_at t l) ->
  forall (G : list ty) (m m' : mtm), rw L t G m m' ->
  forall env : list val, Forall2 has_ty env G -> eval env m = eval env m'.
Proof.
  intros HL G m m' H.
  induction H as
    [G l s m m' Hl Hlen Hs Hm Hm' | G l s m m' Hl Hlen Hs Hm Hm'
    | G o a a' _ IH | G a a' b _ IH | G a b b' _ IH | G a a' _ IH | G a a' _ IH
    | G a a' b _ IH | G a b b' x Hx _ IH]; intros env HE.
  - destruct (args_evaluate G env t HE s Hs) as [vs [Hvs Hn]].
    rewrite (linst_eval env s vs Hn _ _ Hm), (linst_eval env s vs Hn _ _ Hm').
    apply (HL l Hl). rewrite <- Hlen. exact Hvs.
  - destruct (args_evaluate G env t HE s Hs) as [vs [Hvs Hn]].
    rewrite (linst_eval env s vs Hn _ _ Hm), (linst_eval env s vs Hn _ _ Hm').
    symmetry. apply (HL l Hl). rewrite <- Hlen. exact Hvs.
  - simpl. rewrite (IH env HE). reflexivity.
  - simpl. rewrite (IH env HE). reflexivity.
  - simpl. rewrite (IH env HE). reflexivity.
  - simpl. rewrite (IH env HE). reflexivity.
  - simpl. rewrite (IH env HE). reflexivity.
  - simpl. rewrite (IH env HE). reflexivity.
  - simpl. destruct (specialization_is_safe a G env x HE Hx) as [v [Hv Hty]].
    rewrite Hv. apply IH. constructor; assumption.
Qed.

(** Any number of rewrite steps by laws that hold at the member do not change the result. *)
Lemma rewrites_sound (L : list law) (t : ty) :
  (forall l, In l L -> holds_at t l) ->
  forall (G : list ty) (m m' : mtm), rws L t G m m' ->
  forall env : list val, Forall2 has_ty env G -> eval env m = eval env m'.
Proof.
  intros HL G m m' H env HE. induction H as [m | m m' m'' H1 _ IH].
  - reflexivity.
  - rewrite (rewrite_sound L t HL G m m' H1 env HE). exact IH.
Qed.

(** The variables of a law as arguments: the instance that changes nothing. *)
Fixpoint vars (i k : nat) : list mtm :=
  match k with
  | 0 => []
  | S k => MVar i :: vars (S i) k
  end.

Lemma vars_length (k : nat) : forall i, length (vars i k) = k.
Proof.
  induction k as [| k IH]; intros i; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma vars_nth (k : nat) :
  forall (i n : nat) (a : mtm), nth_error (vars i k) n = Some a -> a = MVar (i + n).
Proof.
  induction k as [| k IH]; intros i n a H.
  - destruct n; discriminate.
  - destruct n as [| n]; simpl in H.
    + injection H as <-. rewrite Nat.add_0_r. reflexivity.
    + rewrite Nat.add_succ_r. apply (IH (S i) n a H).
Qed.

Lemma repeat_nth (t : ty) (k : nat) :
  forall n, n < k -> nth_error (repeat t k) n = Some t.
Proof.
  induction k as [| k IH]; intros n H; [lia |].
  destruct n as [| n]; simpl; [reflexivity | apply IH; lia].
Qed.

(** Each variable of a law has the member's type where all of them do. *)
Lemma vars_typed (t : ty) (k : nat) :
  Forall (fun a => mtype (repeat t k) a = Some t) (vars 0 k).
Proof.
  apply Forall_forall. intros a Hin. apply In_nth_error in Hin. destruct Hin as [n Hn].
  assert (Hlt : n < k).
  { rewrite <- (vars_length k 0). apply nth_error_Some. rewrite Hn. discriminate. }
  apply vars_nth in Hn. subst a. simpl. apply repeat_nth. exact Hlt.
Qed.

(** A variable used as its own argument evaluates to its value. *)
Lemma vars_eval (vs : list val) (k : nat) :
  forall n a, nth_error (vars 0 k) n = Some a -> eval vs a = nth_error vs n.
Proof.
  intros n a H. apply vars_nth in H. subst a. reflexivity.
Qed.

(** Whether a side mentions only the first variables of a law.
    - [k:] the number of variables. *)
Fixpoint lscoped (k : nat) (p : lterm) : bool :=
  match p with
  | LVar n => n <? k
  | LPrim _ a => lscoped k a
  | LPair a b => lscoped k a && lscoped k b
  end.

(** A side that mentions only variables with an argument has an instance. *)
Lemma linst_scoped (s : list mtm) (p : lterm) :
  lscoped (length s) p = true -> exists m, linst s p = Some m.
Proof.
  induction p as [n | o a IH | a IHa b IHb]; simpl; intros H.
  - apply Nat.ltb_lt in H. destruct (nth_error s n) as [a |] eqn:E.
    + exists a. reflexivity.
    + apply nth_error_None in E. lia.
  - destruct (IH H) as [m Hm]. exists (MPrim o m). rewrite Hm. reflexivity.
  - apply andb_true_iff in H. destruct H as [Ha Hb].
    destruct (IHa Ha) as [x Hx]. destruct (IHb Hb) as [y Hy].
    exists (MPair x y). rewrite Hx, Hy. reflexivity.
Qed.

(**md
**A rewrite is sound exactly when the law holds.**

A law holds at a member if and only if every rewrite step by it, in every specialization at that
member, leaves the result unchanged. So the law is not merely sufficient. A compiler that
reassociates at a member where associativity fails changes some program, and the evidence for the
law is exactly what the rewrite needs.

- [t:] the member.
- [l:] the law, whose sides mention only its own variables.
*)
Theorem law_iff_rewrite (t : ty) (l : law) :
  lscoped (arity l) (lhs l) = true -> lscoped (arity l) (rhs l) = true ->
  (holds_at t l <->
   forall (G : list ty) (m m' : mtm), rw [l] t G m m' ->
   forall env : list val, Forall2 has_ty env G -> eval env m = eval env m').
Proof.
  intros Hl Hr. split.
  - intros H. apply rewrite_sound. intros l' [E | []]. subst l'. exact H.
  - intros H vs Hvs.
    rewrite <- (vars_length (arity l) 0) in Hl, Hr.
    destruct (linst_scoped _ _ Hl) as [ma Hma]. destruct (linst_scoped _ _ Hr) as [mb Hmb].
    rewrite <- (linst_eval vs _ vs (vars_eval vs (arity l)) _ _ Hma).
    rewrite <- (linst_eval vs _ vs (vars_eval vs (arity l)) _ _ Hmb).
    apply (H (repeat t (arity l))); [| exact Hvs].
    apply (RwLaw [l] t _ l (vars 0 (arity l)) ma mb).
    + left. reflexivity.
    + apply vars_length.
    + apply vars_typed.
    + exact Hma.
    + exact Hmb.
Qed.

(**md
**A definition rewritten by the laws its set carries means what it meant.**

Take a definition that checks, a member set that carries some laws, and any member. A
specialization rewritten by those laws, in any number of steps, returns the value the definition
means at that member, and the value has the declared result type. The laws are checked once per
member, at the constraint. Nothing is checked where the rewrite is applied except the types of
the arguments.

- [C:] the member set of the variable.
- [L:] the laws the set carries.
- [e:] the body.
- [r:] the declared result type.
*)
Theorem rewritten_definition_keeps_meaning
    (C : cset) (L : list law) (G : list oty) (e : tm) (r : oty) :
  check C G e r = true ->
  (forall l, In l L -> carries C l) ->
  forall t : ty, sat t C ->
  forall m m' : mtm, spec t e = Some m -> rws L t (map (inst t) G) m m' ->
  forall env : list val, Forall2 has_ty env (map (inst t) G) ->
  exists v, eval env m' = Some v /\ seval t env e = Some v /\ has_ty v (inst t r).
Proof.
  intros Hc HL t Ht m m' Hs Hrw env HE.
  destruct (checked_definition_runs C G e r Hc t Ht env HE) as [v [Hv Hty]].
  exists v. split; [| split; assumption].
  rewrite <- (rewrites_sound L t (fun l Hl => HL l Hl t Ht) _ m m' Hrw env HE).
  rewrite <- (specialization_preserves_meaning e t m Hs env). exact Hv.
Qed.

(**md ## Rewriting keeps the type

`rewrite_sound` says a rewritten specialization returns the same value. This section says the
checker still accepts it, at the same type. The two are separate obligations. A law that holds at
a member need not be typed there: an operation is an assumption of the model, so two sides of
different types can be equal on every value. What typing needs is a condition on the law's two
sides alone, and it is decided by computing two types.
*)

(** A law is typed at a member when its two sides have one type there. *)
Definition law_typed (t : ty) (l : law) : Prop :=
  exists r, ltype (repeat t (arity l)) (lhs l) = Some r /\
            ltype (repeat t (arity l)) (rhs l) = Some r.

(** A law is type-neutral at a member when the checker gives its two sides the same answer there:
    the same type, or no type for either. *)
Definition type_neutral (t : ty) (l : law) : Prop :=
  ltype (repeat t (arity l)) (lhs l) = ltype (repeat t (arity l)) (rhs l).

(** A law typed at a member is type-neutral there. *)
Lemma law_typed_neutral (t : ty) (l : law) : law_typed t l -> type_neutral t l.
Proof.
  intros [r [Hl Hr]]. unfold type_neutral. rewrite Hl, Hr. reflexivity.
Qed.

Lemma option_ty_eq_dec (a b : option ty) : {a = b} + {a <> b}.
Proof.
  decide equality. apply ty_eq_dec.
Qed.

(** Whether a law is type-neutral at a member is decided by computing the types of its sides. No
    value is examined, so this is a structural check and not a solver query. *)
Lemma type_neutral_dec (t : ty) (l : law) : {type_neutral t l} + {~ type_neutral t l}.
Proof.
  apply option_ty_eq_dec.
Qed.

(** An instance of a side has the side's type, where every argument has the member's type. *)
Lemma linst_type (G : list ty) (t : ty) (s : list mtm) :
  Forall (fun a => mtype G a = Some t) s ->
  forall (p : lterm) (m : mtm), linst s p = Some m ->
  mtype G m = ltype (repeat t (length s)) p.
Proof.
  intros Hs p. rewrite Forall_forall in Hs.
  induction p as [n | o a IH | a IHa b IHb]; intros m Hm; simpl in Hm.
  - simpl. rewrite repeat_nth.
    + apply Hs. apply (nth_error_In s n Hm).
    + apply nth_error_Some. rewrite Hm. discriminate.
  - destruct (linst s a) as [x |]; [| discriminate]. simpl in Hm. injection Hm as <-.
    simpl. rewrite (IH x eq_refl). reflexivity.
  - destruct (linst s a) as [x |]; [| discriminate].
    destruct (linst s b) as [y |]; [| discriminate].
    injection Hm as <-. simpl. rewrite (IHa x eq_refl), (IHb y eq_refl). reflexivity.
Qed.

(**md
**Rewriting by type-neutral laws does not change what the checker says.**

Take a specialization at a member and laws that are type-neutral at that member. A term obtained
by one rewrite step has the type the term had, in the same context, and has no type if the term
had none. The laws need not hold. The proof is by induction on the rewrite step and uses no
assumption about what an operation computes.

- [L:] the laws used.
- [t:] the member.
*)
Theorem rewrite_preserves_type (L : list law) (t : ty) :
  (forall l, In l L -> type_neutral t l) ->
  forall (G : list ty) (m m' : mtm), rw L t G m m' -> mtype G m = mtype G m'.
Proof.
  intros HL G m m' H.
  induction H as
    [G l s m m' Hl Hlen Hs Hm Hm' | G l s m m' Hl Hlen Hs Hm Hm'
    | G o a a' _ IH | G a a' b _ IH | G a b b' _ IH | G a a' _ IH | G a a' _ IH
    | G a a' b _ IH | G a b b' x Hx _ IH].
  - rewrite (linst_type G t s Hs _ _ Hm), (linst_type G t s Hs _ _ Hm'), Hlen.
    apply (HL l Hl).
  - rewrite (linst_type G t s Hs _ _ Hm), (linst_type G t s Hs _ _ Hm'), Hlen.
    symmetry. apply (HL l Hl).
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite Hx. exact IH.
Qed.

(** Any number of rewrite steps by type-neutral laws do not change what the checker says. *)
Lemma rewrites_preserve_type (L : list law) (t : ty) :
  (forall l, In l L -> type_neutral t l) ->
  forall (G : list ty) (m m' : mtm), rws L t G m m' -> mtype G m = mtype G m'.
Proof.
  intros HL G m m' H. induction H as [m | m m' m'' H1 _ IH].
  - reflexivity.
  - rewrite (rewrite_preserves_type L t HL G m m' H1). exact IH.
Qed.

(**md
**A law keeps types exactly when it is type-neutral.**

A law is type-neutral at a member if and only if every rewrite step by it, in every
specialization at that member, leaves the checker's answer unchanged. So the condition cannot be
weakened: a law whose sides differ in type at a member turns some term the checker accepts into
one it rejects or types differently.

- [t:] the member.
- [l:] the law, whose sides mention only its own variables.
*)
Theorem type_neutral_iff_preserving (t : ty) (l : law) :
  lscoped (arity l) (lhs l) = true -> lscoped (arity l) (rhs l) = true ->
  (type_neutral t l <->
   forall (G : list ty) (m m' : mtm), rw [l] t G m m' -> mtype G m = mtype G m').
Proof.
  intros Hl Hr. split.
  - intros H. apply rewrite_preserves_type. intros l' [E | []]. subst l'. exact H.
  - intros H. unfold type_neutral.
    rewrite <- (vars_length (arity l) 0) in Hl, Hr.
    destruct (linst_scoped _ _ Hl) as [ma Hma]. destruct (linst_scoped _ _ Hr) as [mb Hmb].
    pose proof (linst_type (repeat t (arity l)) t _ (vars_typed t (arity l)) _ _ Hma) as Ea.
    pose proof (linst_type (repeat t (arity l)) t _ (vars_typed t (arity l)) _ _ Hmb) as Eb.
    rewrite vars_length in Ea, Eb. rewrite <- Ea, <- Eb.
    apply H. apply (RwLaw [l] t _ l (vars 0 (arity l)) ma mb).
    + left. reflexivity.
    + apply vars_length.
    + apply vars_typed.
    + exact Hma.
    + exact Hmb.
Qed.

(**md
**A definition rewritten by type-neutral laws still has its declared type.**

Take a definition that checks, laws that are type-neutral at every member, and any member. A
specialization rewritten by those laws, in any number of steps, is typed by the checker at the
declared result type. This is type preservation for the rewritten specialization. With
`rewritten_definition_keeps_meaning` it gives both halves: the rewritten term is accepted at the
declared type, and it returns the value the definition means.

- [C:] the member set of the variable.
- [L:] the laws used.
- [e:] the body.
- [r:] the declared result type.
*)
Theorem rewritten_definition_keeps_type
    (C : cset) (L : list law) (G : list oty) (e : tm) (r : oty) :
  check C G e r = true ->
  (forall l t, In l L -> sat t C -> type_neutral t l) ->
  forall t : ty, sat t C ->
  forall m m' : mtm, spec t e = Some m -> rws L t (map (inst t) G) m m' ->
  mtype (map (inst t) G) m' = Some (inst t r).
Proof.
  intros Hc HL t Ht m m' Hs Hrw.
  destruct (derived_satisfaction C G e r Hc t Ht) as [m0 [Hs0 Hm0]].
  rewrite Hs in Hs0. injection Hs0 as <-.
  rewrite <- (rewrites_preserve_type L t (fun l Hl => HL l t Hl Ht) _ m m' Hrw). exact Hm0.
Qed.

(**md
**A rewritten specialization is safe to run, whether or not the laws hold.**

A specialization rewritten by type-neutral laws runs to a value of the declared result type on
every input of the right types. Nothing is assumed about the laws holding. A rewrite by a
type-neutral law that is false at the member may return a different value, but it cannot produce
a stuck program or a value of the wrong type. Safety needs the structural check only. Keeping the
result needs the law. This rests on the assumption that every witness is implemented at its
declared type.

- [C:] the member set of the variable.
- [L:] the laws used.
*)
Corollary rewritten_specialization_is_safe
    (C : cset) (L : list law) (G : list oty) (e : tm) (r : oty) :
  check C G e r = true ->
  (forall l t, In l L -> sat t C -> type_neutral t l) ->
  forall t : ty, sat t C ->
  forall m m' : mtm, spec t e = Some m -> rws L t (map (inst t) G) m m' ->
  forall env : list val, Forall2 has_ty env (map (inst t) G) ->
  exists v, eval env m' = Some v /\ has_ty v (inst t r).
Proof.
  intros Hc HL t Ht m m' Hs Hrw env HE.
  apply (specialization_is_safe m' _ env (inst t r) HE).
  apply (rewritten_definition_keeps_type C L G e r Hc HL t Ht m m' Hs Hrw).
Qed.

(**md ## Theorems per member

A library theorem here derives one law from others. It is stated once, for any type that meets a
side condition, and is used at a member by discharging its premises there.
*)

(** A library theorem: at every type that meets the side condition and at which the premises
    hold, the conclusion holds.
    - [P:] the laws assumed.
    - [c:] the law concluded.
    - [side:] what else is required of the type, such as a witness for an operation. *)
Definition library_theorem (P : list law) (c : law) (side : ty -> Prop) : Prop :=
  forall t, side t -> (forall l, In l P -> holds_at t l) -> holds_at t c.

(**md
**A derivation by rewriting proves a law.**

If one side of an equation can be rewritten into the other by laws that hold at a member, the
equation is a law at that member. This is how a library theorem is proved without looking at any
value: the proof is a sequence of rewrite steps, and `rewrite_sound` makes each step an equality.

- [L:] the laws assumed.
- [n:] the number of variables of the equation.
- [a:] its left side.
- [b:] its right side.
*)
Theorem derived_law (L : list law) (t : ty) (n : nat) (a b : lterm) (ma mb : mtm) :
  (forall l, In l L -> holds_at t l) ->
  linst (vars 0 n) a = Some ma -> linst (vars 0 n) b = Some mb ->
  rws L t (repeat t n) ma mb ->
  holds_at t (Law n a b).
Proof.
  intros HL Ha Hb H vs Hvs. simpl in *.
  rewrite <- (linst_eval vs _ vs (vars_eval vs n) a ma Ha).
  rewrite <- (linst_eval vs _ vs (vars_eval vs n) b mb Hb).
  apply (rewrites_sound L t HL _ ma mb H vs Hvs).
Qed.

(** Reversal of three operands: `(x ∘ y) ∘ z = z ∘ (y ∘ x)`. *)
Definition reversed (o : op) : law :=
  Law 3 (bin o (bin o (LVar 0) (LVar 1)) (LVar 2)) (bin o (LVar 2) (bin o (LVar 1) (LVar 0))).

(**md
**A library theorem, proved once: commutativity gives reversal.**

At any type where an operation takes two values of the type to a value of the type, and is
commutative, three operands may be reversed. The proof is two rewrite steps and mentions no
particular type. The side condition is the witness requirement `shared_operation` already places
on a definition that uses the operation.
*)
Theorem reversal_from_commutativity (o : op) :
  library_theorem [commutative o] (reversed o) (fun t => witness o (TPair t t) = Some t).
Proof.
  intros t Hw HL.
  pose (xy := MPrim o (MPair (MVar 0) (MVar 1))).
  pose (yx := MPrim o (MPair (MVar 1) (MVar 0))).
  apply (derived_law [commutative o] t 3 (lhs (reversed o)) (rhs (reversed o))
           (MPrim o (MPair xy (MVar 2))) (MPrim o (MPair (MVar 2) yx)) HL eq_refl eq_refl).
  apply (RwsStep _ _ _ _ (MPrim o (MPair (MVar 2) xy))).
  - apply (RwLaw _ _ _ (commutative o) [xy; MVar 2]).
    + left. reflexivity.
    + reflexivity.
    + constructor; [simpl; exact Hw |]. constructor; [reflexivity | constructor].
    + reflexivity.
    + reflexivity.
  - apply (RwsStep _ _ _ _ (MPrim o (MPair (MVar 2) yx))); [| apply RwsRefl].
    apply RwPrim. apply RwPairR.
    apply (RwLaw _ _ _ (commutative o) [MVar 0; MVar 1]).
    + left. reflexivity.
    + reflexivity.
    + constructor; [reflexivity |]. constructor; [reflexivity | constructor].
    + reflexivity.
    + reflexivity.
Qed.

(**md
**A library theorem applies to a member set by discharging its premises once per member.**

If every member meets the side condition and the set carries the premises, the set carries the
conclusion. The theorem is not proved again, and no caller of a definition constrained to the set
has anything to discharge.

- [P:] the premises.
- [c:] the conclusion.
- [C:] the member set.
*)
Theorem theorem_per_member (P : list law) (c : law) (side : ty -> Prop) (C : cset) :
  library_theorem P c side ->
  (forall t, sat t C -> side t) ->
  (forall l, In l P -> carries C l) ->
  carries C c.
Proof.
  intros HT Hside HP t Ht. apply HT.
  - apply Hside. exact Ht.
  - intros l Hl. apply (HP l Hl t Ht).
Qed.

(** A member set that carries commutativity of an operation every member has carries reversal. *)
Corollary reversal_at_every_member (C : cset) (o : op) :
  (forall t, sat t C -> witness o (TPair t t) = Some t) ->
  carries C (commutative o) -> carries C (reversed o).
Proof.
  intros Hw Hc.
  apply (theorem_per_member [commutative o] (reversed o) _ C (reversal_from_commutativity o) Hw).
  intros l [E | []]. subst l. exact Hc.
Qed.

(**md ## When evidence must be discharged again

[Conformance §6.1](https://clef-lang.com/spec/draft/conformance/#61-verification-evidence-and-composition)
requires an implementation to invalidate a verified result when a premise, a law, a semantic
interpretation or a program participant changes. For a law at a member, the participants are the
member and the operations, and the interpretation is what each operation computes.
`carries_member` and `law_narrowing` cover a change of members. This section covers a change of
implementation.
*)

(** The witnesses one side of a law uses: each operation with the type of its argument.
    - [G:] the types of the law's variables.
    - [p:] the side. *)
Fixpoint uses (G : list ty) (p : lterm) : list (op * ty) :=
  match p with
  | LVar _ => []
  | LPrim o a =>
      match ltype G a with
      | Some s => (o, s) :: uses G a
      | None => uses G a
      end
  | LPair a b => uses G a ++ uses G b
  end.

(** The witnesses a law uses at a member. *)
Definition law_uses (t : ty) (l : law) : list (op * ty) :=
  uses (repeat t (arity l)) (lhs l) ++ uses (repeat t (arity l)) (rhs l).

(** An implementation is sound when each operation returns a value of its witness's result
    type. *)
Definition sound_impl (I : impl) : Prop :=
  forall (o : op) (a r : ty) (v : val),
    witness o a = Some r -> has_ty v a ->
    exists w, I o v = Some w /\ has_ty w r.

(** The specification's implementation is sound. This is the assumption [witness_sound]. *)
Lemma apply_sound : sound_impl apply.
Proof.
  exact witness_sound.
Qed.

(** A typed side of a law has a value of its type under a sound implementation. *)
Lemma lsafe (I : impl) :
  sound_impl I ->
  forall (G : list ty) (vs : list val), Forall2 has_ty vs G ->
  forall (p : lterm) (r : ty), ltype G p = Some r ->
  exists v, levalI I vs p = Some v /\ has_ty v r.
Proof.
  intros HI G vs HE p. induction p as [n | o a IH | a IHa b IHb]; intros r H; simpl in H.
  - apply (lookup_typed vs G HE n r H).
  - destruct (ltype G a) as [s |] eqn:Hs; [| discriminate].
    destruct (IH s) as [v [Hv Hty]]; [first [exact Hs | reflexivity] |].
    simpl. rewrite Hv. apply (HI o s r v H Hty).
  - destruct (ltype G a) as [x |] eqn:Hx; [| discriminate].
    destruct (ltype G b) as [y |] eqn:Hy; [| discriminate].
    injection H as <-.
    destruct (IHa x) as [u [Hu Hut]]; [first [exact Hx | reflexivity] |].
    destruct (IHb y) as [w [Hw Hwt]]; [first [exact Hy | reflexivity] |].
    simpl. rewrite Hu, Hw. exists (VPair u w). split; [reflexivity | constructor; assumption].
Qed.

(** Two implementations that agree on the witnesses a side uses give it the same value. *)
Lemma leval_agree (I J : impl) :
  sound_impl I ->
  forall (G : list ty) (vs : list val), Forall2 has_ty vs G ->
  forall (p : lterm) (r : ty), ltype G p = Some r ->
  (forall o a, In (o, a) (uses G p) -> forall v, has_ty v a -> I o v = J o v) ->
  levalI I vs p = levalI J vs p.
Proof.
  intros HI G vs HE p. induction p as [n | o a IH | a IHa b IHb]; intros r H HA.
  - reflexivity.
  - simpl in H. destruct (ltype G a) as [s |] eqn:Hs; [| discriminate].
    assert (HU : uses G (LPrim o a) = (o, s) :: uses G a) by (simpl; rewrite Hs; reflexivity).
    rewrite HU in HA.
    assert (E : levalI I vs a = levalI J vs a).
    { apply (IH s); [first [exact Hs | reflexivity] |].
      intros o' a' Hin. apply HA. right. exact Hin. }
    destruct (lsafe I HI G vs HE a s Hs) as [v [Hv Hty]].
    simpl. rewrite <- E, Hv. apply (HA o s); [left; reflexivity | exact Hty].
  - simpl in H. destruct (ltype G a) as [x |] eqn:Hx; [| discriminate].
    destruct (ltype G b) as [y |] eqn:Hy; [| discriminate].
    assert (Ea : levalI I vs a = levalI J vs a).
    { apply (IHa x); [first [exact Hx | reflexivity] |].
      intros o' a' Hin. apply HA. simpl. apply in_or_app. left. exact Hin. }
    assert (Eb : levalI I vs b = levalI J vs b).
    { apply (IHb y); [first [exact Hy | reflexivity] |].
      intros o' a' Hin. apply HA. simpl. apply in_or_app. right. exact Hin. }
    simpl. rewrite Ea, Eb. reflexivity.
Qed.

(**md
**Evidence for a law at a member depends only on the witnesses the law uses there.**

Take a law that holds at a member under one sound implementation, and a second implementation
that agrees with the first on every operation the law uses, at the argument type it uses it at.
The law holds at that member under the second. So when the implementation of an operation changes
at one type, the only obligations to discharge again are those of laws that use that operation at
that type. Evidence for other members, and for laws about other operations, stays valid.

- [I:] the implementation the evidence was established under.
- [J:] the implementation after the change.
- [t:] the member.
- [l:] the law.
*)
Theorem evidence_survives_unrelated_change (I J : impl) (t : ty) (l : law) :
  sound_impl I -> law_typed t l ->
  (forall o a, In (o, a) (law_uses t l) -> forall v, has_ty v a -> I o v = J o v) ->
  holdsI I t l -> holdsI J t l.
Proof.
  intros HI [r [Hl Hr]] HA H vs Hvs. unfold law_uses in HA.
  rewrite <- (leval_agree I J HI _ vs Hvs (lhs l) r Hl
                (fun o a Hin => HA o a (in_or_app _ _ _ (or_introl Hin)))).
  rewrite <- (leval_agree I J HI _ vs Hvs (rhs l) r Hr
                (fun o a Hin => HA o a (in_or_app _ _ _ (or_intror Hin)))).
  apply H. exact Hvs.
Qed.

(**md ## Rules stated in prose

These parts of the extension are not modelled.

1. **Declaring a law.** How a member set states the laws it carries, and whether a law is declared
   on the constraint or on a named member set, is not designed. A declaration would be rejected
   where the law is not type-neutral at some member, which `type_neutral_dec` decides.
2. **Discharging an obligation.** The model takes a discharged obligation as given. Which analysis
   or solver fragment decides a law at a member, and what happens when it cannot, is the
   specification's Tier 2 question and is not answered here.
3. **Choosing a rewrite.** The model says which rewrites are sound. It does not say which a
   compiler performs.
*)
