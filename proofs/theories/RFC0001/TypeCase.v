From Stdlib Require Import List Bool.
Import ListNotations.
From Clef Require Import Spec.Types Spec.Runtime Spec.Witnesses RFC0001.Constraints.

(**md # Checking the body and the static type-case

A definition with a set-constrained type variable is checked once, where it is defined, against
every member. This module models such a definition as a term over one type variable, gives the
check, and proves what a passing check guarantees about every instantiation.

```fsharp
let describe<'T when 'T : (int | string)> (x: 'T) : string =
    match x with
    | :? int as i -> formatInt i
    | :? string as s -> s
```
*)

(**md ## Source terms

The body of a definition that is generic in one set-constrained type variable. Variables are
numbered from the innermost binder. Terms carry no types, except for the type each arm of a
type-case tests.

`Case` is the static type-case on the constrained variable. An arm is the tested type and the
result expression. Inside an arm the variable equals the tested type, so a value of the variable's
type is used there at the tested type, which is what `:? int as i` binds.
*)
Inductive tm : Type :=
| Var (n : nat)
| Prim (o : op) (e : tm)
| Pair (a b : tm)
| Fst (e : tm)
| Snd (e : tm)
| Let (a b : tm)
| Case (arms : list (ty * tm)).

(** Induction over terms that also covers the result expression of every arm. *)
Section TmInduction.
  Variable P : tm -> Prop.
  Hypothesis HVar : forall n, P (Var n).
  Hypothesis HPrim : forall o e, P e -> P (Prim o e).
  Hypothesis HPair : forall a b, P a -> P b -> P (Pair a b).
  Hypothesis HFst : forall e, P e -> P (Fst e).
  Hypothesis HSnd : forall e, P e -> P (Snd e).
  Hypothesis HLet : forall a b, P a -> P b -> P (Let a b).
  Hypothesis HCase : forall arms, Forall (fun arm => P (snd arm)) arms -> P (Case arms).

  Fixpoint tm_arms_ind (e : tm) : P e :=
    match e with
    | Var n => HVar n
    | Prim o a => HPrim o a (tm_arms_ind a)
    | Pair a b => HPair a b (tm_arms_ind a) (tm_arms_ind b)
    | Fst a => HFst a (tm_arms_ind a)
    | Snd a => HSnd a (tm_arms_ind a)
    | Let a b => HLet a b (tm_arms_ind a) (tm_arms_ind b)
    | Case arms =>
        HCase arms
          ((fix go (l : list (ty * tm)) : Forall (fun arm => P (snd arm)) l :=
              match l with
              | [] => Forall_nil _
              | (u, a) :: r => Forall_cons (u, a) (tm_arms_ind a) (go r)
              end) arms)
    end.
End TmInduction.

(**md ## Specialized terms

What a specialization of the body is made of. There is no type-case here, and no type: a
specialized term cannot test a type at run time, because the language it is written in has no such
construct.
*)
Inductive mtm : Type :=
| MVar (n : nat)
| MPrim (o : op) (e : mtm)
| MPair (a b : mtm)
| MFst (e : mtm)
| MSnd (e : mtm)
| MLet (a b : mtm).

(** The type of a specialized term, or [None] when it has none. An operation is typed by its
    witness at the type of its argument.
    - [G:] the types of the variables in scope, innermost first.
    - [m:] the term. *)
Fixpoint mtype (G : list ty) (m : mtm) : option ty :=
  match m with
  | MVar n => nth_error G n
  | MPrim o e =>
      match mtype G e with
      | Some a => witness o a
      | None => None
      end
  | MPair a b =>
      match mtype G a, mtype G b with
      | Some x, Some y => Some (TPair x y)
      | _, _ => None
      end
  | MFst e =>
      match mtype G e with
      | Some (TPair x _) => Some x
      | _ => None
      end
  | MSnd e =>
      match mtype G e with
      | Some (TPair _ y) => Some y
      | _ => None
      end
  | MLet a b =>
      match mtype G a with
      | Some x => mtype (x :: G) b
      | None => None
      end
  end.

(**md ## Specialization

Saturation produces one specialization of the body per instantiating type. Each type-case reduces
to the arm whose tested type is the instantiating type, and the other arms are discarded.
*)

(** The result expression of the first arm that tests a type.
    - [t:] the type looked for.
    - [arms:] the arms searched. *)
Fixpoint pick (t : ty) (arms : list (ty * tm)) : option tm :=
  match arms with
  | [] => None
  | (u, a) :: r => if ty_eq_dec t u then Some a else pick t r
  end.

(** The specialization of a body at a type, or [None] when a type-case has no arm for it.
    - [t:] the instantiating type.
    - [e:] the body. *)
Fixpoint spec (t : ty) (e : tm) : option mtm :=
  match e with
  | Var n => Some (MVar n)
  | Prim o a => option_map (MPrim o) (spec t a)
  | Pair a b =>
      match spec t a, spec t b with
      | Some x, Some y => Some (MPair x y)
      | _, _ => None
      end
  | Fst a => option_map MFst (spec t a)
  | Snd a => option_map MSnd (spec t a)
  | Let a b =>
      match spec t a, spec t b with
      | Some x, Some y => Some (MLet x y)
      | _, _ => None
      end
  | Case arms =>
      (fix go (l : list (ty * tm)) : option mtm :=
         match l with
         | [] => None
         | (u, a) :: r => if ty_eq_dec t u then spec t a else go r
         end) arms
  end.

(** Specializing a type-case is specializing the arm picked for the instantiating type. *)
Lemma spec_case (t : ty) (arms : list (ty * tm)) :
  spec t (Case arms) =
  match pick t arms with
  | Some a => spec t a
  | None => None
  end.
Proof.
  simpl. induction arms as [| [u a] r IH].
  - reflexivity.
  - simpl. destruct (ty_eq_dec t u).
    + reflexivity.
    + exact IH.
Qed.

(**md ## The definition-site check *)

(** An instantiation of the body is well typed when it specializes, and the specialization has the
    declared result type at that instantiation.
    - [t:] the instantiating type.
    - [G:] the types of the parameters, which may mention the variable.
    - [e:] the body.
    - [r:] the declared result type, which may mention the variable. *)
Definition well_typed_at (t : ty) (G : list oty) (e : tm) (r : oty) : Prop :=
  exists m, spec t e = Some m /\ mtype (map (inst t) G) m = Some (inst t r).

(** The check of one member, as the compiler computes it. *)
Definition instance_ok (G : list oty) (e : tm) (r : oty) (t : ty) : bool :=
  match spec t e with
  | Some m =>
      match mtype (map (inst t) G) m with
      | Some a => if ty_eq_dec a (inst t r) then true else false
      | None => false
      end
  | None => false
  end.

(** The check of a definition: every member is checked, at the definition.
    - [C:] the member set of the variable. *)
Definition check (C : cset) (G : list oty) (e : tm) (r : oty) : bool :=
  forallb (instance_ok G e r) C.

(** The computed check of one member agrees with well-typedness at that member. *)
Lemma instance_ok_iff (G : list oty) (e : tm) (r : oty) (t : ty) :
  instance_ok G e r t = true <-> well_typed_at t G e r.
Proof.
  unfold instance_ok, well_typed_at. split.
  - destruct (spec t e) as [m |] eqn:Hs; [| discriminate].
    destruct (mtype (map (inst t) G) m) as [a |] eqn:Hm; [| discriminate].
    destruct (ty_eq_dec a (inst t r)) as [E | N]; [| discriminate].
    intros _. exists m. split; [reflexivity | rewrite Hm, E; reflexivity].
  - intros [m [Hs Ht]]. rewrite Hs, Ht.
    destruct (ty_eq_dec (inst t r) (inst t r)) as [_ | N]; [reflexivity | contradiction].
Qed.

(**md
**A definition that checks is well typed at every instantiation.**

This is derived satisfaction. When the check passes at the definition, every type that satisfies
the constraint yields a specialization with the declared type. A call site is never the first place
where an operation on the constrained variable is found unsupported.

- [C:] the member set of the variable.
- [G:] the types of the parameters.
- [e:] the body.
- [r:] the declared result type.
*)
Theorem derived_satisfaction (C : cset) (G : list oty) (e : tm) (r : oty) :
  check C G e r = true -> forall t, sat t C -> well_typed_at t G e r.
Proof.
  unfold check, sat. intros H t Ht.
  rewrite forallb_forall in H. apply instance_ok_iff. apply H. exact Ht.
Qed.

(**md
**The check rejects only definitions that fail at some member.**

When the check fails, there is a member at which the body is not well typed. The diagnostic can
name it.
*)
Theorem check_complete (C : cset) (G : list oty) (e : tm) (r : oty) :
  (forall t, sat t C -> well_typed_at t G e r) -> check C G e r = true.
Proof.
  unfold check, sat. intros H. apply forallb_forall. intros t Ht.
  apply instance_ok_iff. apply H. exact Ht.
Qed.

(**md
**Narrowing a constraint keeps a definition valid.**

A body that checks against a member set checks against every set that entails it. Removing a member
from a constraint never breaks the definition, so only adding one can.

- [C:] the narrower member set.
- [D:] the member set the body was checked against.
*)
Theorem check_narrowing (C D : cset) (G : list oty) (e : tm) (r : oty) :
  entails C D -> check D G e r = true -> check C G e r = true.
Proof.
  intros HE HD. apply check_complete. intros t Ht.
  apply (derived_satisfaction D); [exact HD |].
  apply (proj1 (entails_iff_sat C D) HE). exact Ht.
Qed.

(**md
**A constrained variable may instantiate any definition its constraint entails.**

Inside a body whose variable has one member set, calling a definition that was checked against
another is sound when the first entails the second. Every type the caller can be instantiated to is
one the callee was checked at.

- [C:] the member set of the caller's variable.
- [D:] the member set of the callee's variable.
*)
Theorem call_through_entailment (C D : cset) (G : list oty) (e : tm) (r : oty) :
  entails C D -> check D G e r = true -> forall t, sat t C -> well_typed_at t G e r.
Proof.
  intros HE HD. apply derived_satisfaction. apply (check_narrowing C D); assumption.
Qed.

(**md ## Shared operations *)

(**md
**An operation is accepted exactly when every member has a witness for it.**

A body that applies one operation to its parameter checks if and only if each member has a witness
for that operation with the declared result type. The result type may mention the variable, which
is how `x + x` has type `'T` at both `int` and `float`.

- [o:] the operation applied.
- [r:] the declared result type.
*)
Theorem shared_operation (C : cset) (o : op) (r : oty) :
  check C [OVar] (Prim o (Var 0)) r = true <->
  forall t, sat t C -> witness o t = Some (inst t r).
Proof.
  split.
  - intros H t Ht. destruct (derived_satisfaction _ _ _ _ H t Ht) as [m [Hs Hm]].
    simpl in Hs. injection Hs as <-. simpl in Hm. exact Hm.
  - intros H. apply check_complete. intros t Ht.
    exists (MPrim o (MVar 0)). split; [reflexivity |]. simpl. apply H. exact Ht.
Qed.

(**md ## What a definition means

The reference meaning of a definition is given with the instantiating type at hand: evaluating a
type-case looks at that type and takes its arm. This is how a compiler that passed types at run
time would run the body. It is the specification of behaviour, not the implementation.
*)

(** The value of a body at an instantiating type, or [None] where evaluation is stuck.
    - [t:] the instantiating type, which a type-case inspects.
    - [env:] the values of the variables in scope, innermost first.
    - [e:] the body. *)
Fixpoint seval (t : ty) (env : list val) (e : tm) : option val :=
  match e with
  | Var n => nth_error env n
  | Prim o a =>
      match seval t env a with
      | Some v => apply o v
      | None => None
      end
  | Pair a b =>
      match seval t env a, seval t env b with
      | Some x, Some y => Some (VPair x y)
      | _, _ => None
      end
  | Fst a =>
      match seval t env a with
      | Some (VPair x _) => Some x
      | _ => None
      end
  | Snd a =>
      match seval t env a with
      | Some (VPair _ y) => Some y
      | _ => None
      end
  | Let a b =>
      match seval t env a with
      | Some x => seval t (x :: env) b
      | None => None
      end
  | Case arms =>
      (fix go (l : list (ty * tm)) : option val :=
         match l with
         | [] => None
         | (u, a) :: r => if ty_eq_dec t u then seval t env a else go r
         end) arms
  end.

(** Evaluating a type-case is evaluating the arm picked for the instantiating type. *)
Lemma seval_case (t : ty) (env : list val) (arms : list (ty * tm)) :
  seval t env (Case arms) =
  match pick t arms with
  | Some a => seval t env a
  | None => None
  end.
Proof.
  simpl. induction arms as [| [u a] r IH].
  - reflexivity.
  - simpl. destruct (ty_eq_dec t u).
    + reflexivity.
    + exact IH.
Qed.

(** A picked result expression belongs to one of the arms. *)
Lemma pick_in (t : ty) (arms : list (ty * tm)) (a : tm) :
  pick t arms = Some a -> In (t, a) arms.
Proof.
  induction arms as [| [u b] r IH]; simpl; intros H.
  - discriminate.
  - destruct (ty_eq_dec t u) as [E | N].
    + injection H as <-. subst u. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(**md ## What a specialization computes

A specialization is given no type. It is evaluated from the values of its variables alone.
*)

(** The value of a specialized term, or [None] where evaluation is stuck.
    - [env:] the values of the variables in scope, innermost first.
    - [m:] the term. *)
Fixpoint eval (env : list val) (m : mtm) : option val :=
  match m with
  | MVar n => nth_error env n
  | MPrim o e =>
      match eval env e with
      | Some v => apply o v
      | None => None
      end
  | MPair a b =>
      match eval env a, eval env b with
      | Some x, Some y => Some (VPair x y)
      | _, _ => None
      end
  | MFst e =>
      match eval env e with
      | Some (VPair x _) => Some x
      | _ => None
      end
  | MSnd e =>
      match eval env e with
      | Some (VPair _ y) => Some y
      | _ => None
      end
  | MLet a b =>
      match eval env a with
      | Some x => eval (x :: env) b
      | None => None
      end
  end.

(**md
**A specialization computes what the definition means, without being told the type.**

Whenever a body specializes at a type, the specialization returns exactly what the reference
meaning returns at that type, on every input. The reference meaning inspects the instantiating
type and the specialization has no access to it. The static type-case is therefore erased
completely: no run-time test, tag or type argument is needed to implement it.

- [e:] the body.
*)
Theorem specialization_preserves_meaning (e : tm) :
  forall (t : ty) (m : mtm), spec t e = Some m ->
  forall env : list val, seval t env e = eval env m.
Proof.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | arms IH]
    using tm_arms_ind; intros t m H env.
  - simpl in H. injection H as <-. reflexivity.
  - simpl in H. destruct (spec t e) as [x |] eqn:Hx; [| discriminate].
    simpl in H. injection H as <-. simpl. rewrite (IH t x Hx env). reflexivity.
  - simpl in H. destruct (spec t a) as [x |] eqn:Hx; [| discriminate].
    destruct (spec t b) as [y |] eqn:Hy; [| discriminate].
    injection H as <-. simpl. rewrite (IHa t x Hx env), (IHb t y Hy env). reflexivity.
  - simpl in H. destruct (spec t e) as [x |] eqn:Hx; [| discriminate].
    simpl in H. injection H as <-. simpl. rewrite (IH t x Hx env). reflexivity.
  - simpl in H. destruct (spec t e) as [x |] eqn:Hx; [| discriminate].
    simpl in H. injection H as <-. simpl. rewrite (IH t x Hx env). reflexivity.
  - simpl in H. destruct (spec t a) as [x |] eqn:Hx; [| discriminate].
    destruct (spec t b) as [y |] eqn:Hy; [| discriminate].
    injection H as <-. simpl. rewrite (IHa t x Hx env).
    destruct (eval env x) as [v |]; [| reflexivity]. apply (IHb t y Hy).
  - rewrite spec_case in H. rewrite seval_case.
    destruct (pick t arms) as [a |] eqn:Hp; [| discriminate].
    rewrite Forall_forall in IH. apply (IH (t, a) (pick_in t arms a Hp) t m H env).
Qed.

(** A variable that has a type in scope has a value of that type in a matching environment. *)
Lemma lookup_typed (env : list val) (G : list ty) :
  Forall2 has_ty env G ->
  forall (n : nat) (t : ty), nth_error G n = Some t ->
  exists v, nth_error env n = Some v /\ has_ty v t.
Proof.
  induction 1 as [| v s env G Hv HE IH]; intros n t H.
  - destruct n; discriminate.
  - destruct n as [| n]; simpl in *.
    + injection H as <-. exists v. split; [reflexivity | exact Hv].
    + apply IH. exact H.
Qed.

(**md
**A typed specialization runs to a value of its type.**

Evaluation of a specialization that has a type never gets stuck, and the value it returns has that
type. This rests on the assumption that every witness is implemented at its declared type.

- [m:] the specialization.
*)
Theorem specialization_is_safe (m : mtm) :
  forall (G : list ty) (env : list val) (t : ty),
    Forall2 has_ty env G -> mtype G m = Some t ->
    exists v, eval env m = Some v /\ has_ty v t.
Proof.
  induction m as [n | o m IH | a IHa b IHb | m IH | m IH | a IHa b IHb];
    intros G env t HE HT; simpl in *.
  - apply (lookup_typed env G HE n t HT).
  - destruct (mtype G m) as [s |] eqn:Hs; [| discriminate].
    destruct (IH G env s HE Hs) as [v [Hv Hty]]. rewrite Hv.
    apply (witness_sound o s t v HT Hty).
  - destruct (mtype G a) as [s |] eqn:Hs; [| discriminate].
    destruct (mtype G b) as [u |] eqn:Hu; [| discriminate].
    injection HT as <-.
    destruct (IHa G env s HE Hs) as [x [Hx Hxt]].
    destruct (IHb G env u HE Hu) as [y [Hy Hyt]].
    rewrite Hx, Hy. exists (VPair x y). split; [reflexivity | constructor; assumption].
  - destruct (mtype G m) as [[c | p q | p q] |] eqn:Hs; try discriminate.
    injection HT as <-.
    destruct (IH G env (TPair p q) HE Hs) as [v [Hv Hty]]. rewrite Hv.
    inversion Hty as [| x y ? ? Hxt Hyt]; subst.
    exists x. split; [reflexivity | exact Hxt].
  - destruct (mtype G m) as [[c | p q | p q] |] eqn:Hs; try discriminate.
    injection HT as <-.
    destruct (IH G env (TPair p q) HE Hs) as [v [Hv Hty]]. rewrite Hv.
    inversion Hty as [| x y ? ? Hxt Hyt]; subst.
    exists y. split; [reflexivity | exact Hyt].
  - destruct (mtype G a) as [s |] eqn:Hs; [| discriminate].
    destruct (IHa G env s HE Hs) as [x [Hx Hxt]]. rewrite Hx.
    apply (IHb (s :: G) (x :: env) t); [constructor; assumption | exact HT].
Qed.

(**md
**A definition that checks runs to a value at every member.**

Take a definition whose check passes, any type satisfying its constraint, and arguments of the
parameter types at that type. The definition's meaning at that type is a value of the declared
result type. The check at the definition is all that is needed: nothing is checked again at a call
site or at run time.

- [C:] the member set of the variable.
- [G:] the types of the parameters.
- [e:] the body.
- [r:] the declared result type.
*)
Theorem checked_definition_runs (C : cset) (G : list oty) (e : tm) (r : oty) :
  check C G e r = true ->
  forall t : ty, sat t C ->
  forall env : list val, Forall2 has_ty env (map (inst t) G) ->
  exists v, seval t env e = Some v /\ has_ty v (inst t r).
Proof.
  intros H t Ht env HE.
  destruct (derived_satisfaction C G e r H t Ht) as [m [Hs Hm]].
  rewrite (specialization_preserves_meaning e t m Hs env).
  apply (specialization_is_safe m (map (inst t) G) env (inst t r) HE Hm).
Qed.

(**md ## Bodies with no type-case *)

(** Whether a body uses no type-case. *)
Fixpoint case_free (e : tm) : bool :=
  match e with
  | Var _ => true
  | Prim _ a => case_free a
  | Pair a b => case_free a && case_free b
  | Fst a => case_free a
  | Snd a => case_free a
  | Let a b => case_free a && case_free b
  | Case _ => false
  end.

(**md
**A body with no type-case is the same code at every instantiation.**

Its specialization does not depend on the instantiating type. Only a type-case can make a
set-constrained definition behave differently per member, so the loss of uniformity is confined to
bodies that ask for it.
*)
Theorem case_free_uniform (e : tm) :
  case_free e = true -> exists m, forall t, spec t e = Some m.
Proof.
  induction e as [n | o e IH | a IHa b IHb | e IH | e IH | a IHa b IHb | arms]; simpl; intros H.
  - exists (MVar n). reflexivity.
  - destruct (IH H) as [m Hm]. exists (MPrim o m). intros t. rewrite Hm. reflexivity.
  - apply andb_true_iff in H. destruct H as [Ha Hb].
    destruct (IHa Ha) as [x Hx]. destruct (IHb Hb) as [y Hy].
    exists (MPair x y). intros t. rewrite Hx, Hy. reflexivity.
  - destruct (IH H) as [m Hm]. exists (MFst m). intros t. rewrite Hm. reflexivity.
  - destruct (IH H) as [m Hm]. exists (MSnd m). intros t. rewrite Hm. reflexivity.
  - apply andb_true_iff in H. destruct H as [Ha Hb].
    destruct (IHa Ha) as [x Hx]. destruct (IHb Hb) as [y Hy].
    exists (MLet x y). intros t. rewrite Hx, Hy. reflexivity.
  - discriminate.
Qed.

(**md
**A body with no type-case cannot observe its instantiation.**

Its meaning is the same at every type, on every input. A set-constrained definition that does not
use a type-case is as uniform as an unconstrained one.

- [t:] one instantiating type.
- [u:] another.
*)
Theorem case_free_parametric (e : tm) (t u : ty) (env : list val) :
  case_free e = true -> seval t env e = seval u env e.
Proof.
  intros H. destruct (case_free_uniform e H) as [m Hm].
  rewrite (specialization_preserves_meaning e t m (Hm t) env).
  rewrite (specialization_preserves_meaning e u m (Hm u) env).
  reflexivity.
Qed.

(**md ## Coverage

The arms of a type-case are complete when every member is tested. Inside an arm the variable is one
type, so a type-case nested in that arm needs an arm for that type alone.
*)

(** Whether every type-case in a body has an arm for each type the variable can be.
    - [C:] the types the variable can be at this point of the body. *)
Fixpoint covered (C : cset) (e : tm) : Prop :=
  match e with
  | Var _ => True
  | Prim _ a => covered C a
  | Pair a b => covered C a /\ covered C b
  | Fst a => covered C a
  | Snd a => covered C a
  | Let a b => covered C a /\ covered C b
  | Case arms =>
      (forall t, In t C -> In t (map fst arms)) /\
      (fix go (l : list (ty * tm)) : Prop :=
         match l with
         | [] => True
         | (u, a) :: r => covered [u] a /\ go r
         end) arms
  end.

(**md
**A covered body specializes at every member.**

When each type-case tests every member, saturation finds an arm for every instantiating type that
satisfies the constraint. No instantiation is left without code.
*)
Theorem coverage_total (e : tm) :
  forall C, covered C e -> forall t, sat t C -> exists m, spec t e = Some m.
Proof.
  unfold sat.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | arms IH]
    using tm_arms_ind; intros C H t Ht.
  - exists (MVar n). reflexivity.
  - destruct (IH C H t Ht) as [m Hm]. exists (MPrim o m). simpl. rewrite Hm. reflexivity.
  - destruct H as [Ha Hb].
    destruct (IHa C Ha t Ht) as [x Hx]. destruct (IHb C Hb t Ht) as [y Hy].
    exists (MPair x y). simpl. rewrite Hx, Hy. reflexivity.
  - destruct (IH C H t Ht) as [m Hm]. exists (MFst m). simpl. rewrite Hm. reflexivity.
  - destruct (IH C H t Ht) as [m Hm]. exists (MSnd m). simpl. rewrite Hm. reflexivity.
  - destruct H as [Ha Hb].
    destruct (IHa C Ha t Ht) as [x Hx]. destruct (IHb C Hb t Ht) as [y Hy].
    exists (MLet x y). simpl. rewrite Hx, Hy. reflexivity.
  - rewrite spec_case. destruct H as [Hall Hin]. specialize (Hall t Ht).
    clear Ht. induction arms as [| [u a] r IHr].
    + contradiction.
    + simpl. inversion IH as [| ? ? Pa Pr]; subst. destruct Hin as [Ha Hr].
      destruct (ty_eq_dec t u) as [E | N].
      * subst u. apply (Pa [t] Ha). left. reflexivity.
      * apply IHr; [exact Pr | | exact Hr].
        destruct Hall as [E | Hin']; [symmetry in E; contradiction | exact Hin'].
Qed.

(**md ## Rules stated in prose

These rules of the static type-case are part of the design and are not modelled here.

1. **Admissible tests.** The type in a `:?` pattern is a member of the set. A test against any
   other type is an error.
2. **Locality.** The equation between the variable and the tested type is not used to solve an
   inference variable that is not local to the arm. Where the result type of the `match` depends on
   the arm taken, it is fixed before the arms are checked, by annotation or from context.
3. **Parametricity.** A `:?` pattern whose input has the type of a variable with no closed-set
   constraint is an error. An unconstrained type variable stays parametric.
4. **Scope.** The pattern input has the type of the constrained variable itself, not a type
   constructed from it. Only the pattern form is specified.
*)
