From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.
From Clef Require Import Spec.Types Spec.Runtime Spec.Witnesses.
From Clef Require Import RFC0001.Constraints RFC0001.TypeCase RFC0002.Regions RFC0002.Bodies.

(**md # A type-case nested in an arm

[Bodies](Clef.RFC0002.Bodies.html) gives each arm a body with no type-case of its own. This module
removes that limit. A match may appear anywhere in a body, on any scrutinee, and its arms may hold
further matches.

```fsharp
let g<'A, 'B, 'T when 'A : (int | string)
                 and 'B : (string | float)
                 and 'T : ('A | 'B)> (x: 'T) (y: 'T) : 'T =
    match x with
    | :? 'A as a ->
        match y with
        | :? 'A as c -> c      // one arm is enough here: 'T is 'A in this region
    | :? 'B as b -> b
```

Four questions are answered.

1. Is a nested type-case still erased? A specialization has no type to inspect, at any depth.
2. Is a definition that checks still safe to run at every instantiation?
3. What does an inner match know about the arm it is in?
4. Does the model agree with [Bodies](Clef.RFC0002.Bodies.html) where there is no nesting?

Only the equation reading is modelled, since it is the one the RFC adopts. A test `:? 'A` on a
scrutinee succeeds when the scrutinee's type is the type `'A` is instantiated to.
*)

(**md ## Terms

A body is a term in which a match may occur anywhere. Variables are numbered from the innermost
binder. The scrutinee of a definition is variable zero of its body, and the other parameters
follow it.
*)
Inductive ntm : Type :=
| NVar (n : nat)
| NPrim (o : op) (e : ntm)
| NPair (a b : ntm)
| NFst (e : ntm)
| NSnd (e : ntm)
| NLet (a b : ntm)
| NMatch (e : ntm) (arms : list (test * ntm)).

(** Induction over terms that also covers the scrutinee and the body of every arm of a match. *)
Section NtmInduction.
  Variable P : ntm -> Prop.
  Hypothesis HVar : forall n, P (NVar n).
  Hypothesis HPrim : forall o e, P e -> P (NPrim o e).
  Hypothesis HPair : forall a b, P a -> P b -> P (NPair a b).
  Hypothesis HFst : forall e, P e -> P (NFst e).
  Hypothesis HSnd : forall e, P e -> P (NSnd e).
  Hypothesis HLet : forall a b, P a -> P b -> P (NLet a b).
  Hypothesis HMatch : forall e arms,
    P e -> Forall (fun arm => P (snd arm)) arms -> P (NMatch e arms).

  Fixpoint ntm_arms_ind (e : ntm) : P e :=
    match e with
    | NVar n => HVar n
    | NPrim o a => HPrim o a (ntm_arms_ind a)
    | NPair a b => HPair a b (ntm_arms_ind a) (ntm_arms_ind b)
    | NFst a => HFst a (ntm_arms_ind a)
    | NSnd a => HSnd a (ntm_arms_ind a)
    | NLet a b => HLet a b (ntm_arms_ind a) (ntm_arms_ind b)
    | NMatch a arms =>
        HMatch a arms (ntm_arms_ind a)
          ((fix go (l : list (test * ntm)) : Forall (fun arm => P (snd arm)) l :=
              match l with
              | [] => Forall_nil _
              | (p, b) :: r => Forall_cons (p, b) (ntm_arms_ind b) (go r)
              end) arms)
    end.
End NtmInduction.

(**md ## A test on any scrutinee

In [Regions](Clef.RFC0002.Regions.html) the scrutinee is the parameter of type `'T`. A nested
match may scrutinise any term, so a test is taken against the type the scrutinee has at the
instantiation.
*)

(** Whether a test succeeds on a scrutinee of a given type, under the equation reading.
    - [s:] the instantiation.
    - [u:] the type of the scrutinee at that instantiation.
    - [p:] the test. *)
Fixpoint holds (s : inst3) (u : ty) (p : test) : bool :=
  match p with
  | IsA => tyeqb u (iA s)
  | IsB => tyeqb u (iB s)
  | Both p q => holds s u p && holds s u q
  end.

(** On the parameter of type `'T`, this is the test of Regions under the equation reading. *)
Lemma holds_scrutinee (CA CB : cset) (s : inst3) (p : test) :
  holds s (iT s) p = matches Equation CA CB s p.
Proof.
  induction p as [| | p1 IH1 p2 IH2]; simpl; [reflexivity | reflexivity |].
  rewrite IH1, IH2. reflexivity.
Qed.

(** Every test introduces at least one binder. *)
Lemma arity_pos (p : test) : exists j, arity p = S j.
Proof.
  induction p as [| | p1 IH1 p2 IH2]; simpl.
  - exists 0. reflexivity.
  - exists 0. reflexivity.
  - destruct IH1 as [j ->]. exists (j + arity p2). reflexivity.
Qed.

(** An arm has as many binder types as binders. *)
Lemma binder_length (s : inst3) (p : test) : length (binder_types s p) = arity p.
Proof.
  induction p as [| | p1 IH1 p2 IH2]; simpl; [reflexivity | reflexivity |].
  rewrite length_app, IH1, IH2. reflexivity.
Qed.

(** Where a test succeeds, every binder of the arm is at the scrutinee's type. This is
    `equation_refines` for a scrutinee of any type. *)
Lemma holds_binders (s : inst3) (u : ty) (p : test) :
  holds s u p = true -> binder_types s p = repeat u (arity p).
Proof.
  induction p as [| | p1 IH1 p2 IH2]; simpl; intros H.
  - apply tyeqb_iff in H. rewrite H. reflexivity.
  - apply tyeqb_iff in H. rewrite H. reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    rewrite (IH1 H1), (IH2 H2), repeat_app. reflexivity.
Qed.

Lemma repeat_shift {A : Type} (v : A) (k : nat) (l : list A) :
  repeat v k ++ v :: l = v :: repeat v k ++ l.
Proof.
  induction k as [| k IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** The context of an arm's body, with the first binder written last. *)
Lemma binder_ctx (s : inst3) (u : ty) (p : test) (G : list ty) :
  holds s u p = true ->
  binder_types s p ++ G = repeat u (pred (arity p)) ++ u :: G.
Proof.
  intros H. rewrite (holds_binders s u p H). destruct (arity_pos p) as [j ->].
  simpl. rewrite repeat_shift. reflexivity.
Qed.

(** The values of an arm's binders, with the first binder written last. *)
Lemma binder_env (v : val) (p : test) (env : list val) :
  repeat v (arity p) ++ env = repeat v (pred (arity p)) ++ v :: env.
Proof.
  destruct (arity_pos p) as [j ->]. simpl. rewrite repeat_shift. reflexivity.
Qed.

(** The innermost binder of an arm that matches has the scrutinee's type. *)
Lemma binder_head (s : inst3) (u : ty) (p : test) (G : list ty) :
  holds s u p = true -> nth_error (binder_types s p ++ G) 0 = Some u.
Proof.
  intros H. rewrite (holds_binders s u p H). destruct (arity_pos p) as [j ->]. reflexivity.
Qed.

(** The innermost binder of an arm holds the scrutinee. *)
Lemma repeat_head (v : val) (p : test) (env : list val) :
  nth_error (repeat v (arity p) ++ env) 0 = Some v.
Proof.
  destruct (arity_pos p) as [j ->]. reflexivity.
Qed.

(**md ## Typing a body at an instantiation

A body is typed at one instantiation, in a context of closed types. A match is typed by typing
its scrutinee, selecting the first arm whose test succeeds on that type, and typing that arm's
body with the arm's binders in scope. An arm whose test fails at the instantiation is not looked
at there.

This asks less than the check of Bodies, which types every arm that matches. It is enough for
safety. The questions about arm order are not asked again here.
*)

(** The type of a body at an instantiation, or [None] when it has none.
    - [s:] the instantiation.
    - [G:] the types of the variables in scope, innermost first.
    - [e:] the body. *)
Fixpoint ntype (s : inst3) (G : list ty) (e : ntm) : option ty :=
  match e with
  | NVar n => nth_error G n
  | NPrim o a =>
      match ntype s G a with
      | Some x => witness o x
      | None => None
      end
  | NPair a b =>
      match ntype s G a, ntype s G b with
      | Some x, Some y => Some (TPair x y)
      | _, _ => None
      end
  | NFst a =>
      match ntype s G a with
      | Some (TPair x _) => Some x
      | _ => None
      end
  | NSnd a =>
      match ntype s G a with
      | Some (TPair _ y) => Some y
      | _ => None
      end
  | NLet a b =>
      match ntype s G a with
      | Some x => ntype s (x :: G) b
      | None => None
      end
  | NMatch a arms =>
      match ntype s G a with
      | Some u =>
          (fix go (l : list (test * ntm)) : option ty :=
             match l with
             | [] => None
             | (p, b) :: r =>
                 if holds s u p then ntype s (binder_types s p ++ G) b else go r
             end) arms
      | None => None
      end
  end.

(** The arm a match selects on a scrutinee of a given type: the first whose test succeeds. *)
Definition pickn (s : inst3) (u : ty) (arms : list (test * ntm)) : option (test * ntm) :=
  find (fun a => holds s u (fst a)) arms.

(** Typing a match is typing the body of the arm selected. *)
Lemma ntype_match (s : inst3) (G : list ty) (a : ntm) (arms : list (test * ntm)) :
  ntype s G (NMatch a arms) =
  match ntype s G a with
  | Some u =>
      match pickn s u arms with
      | Some (p, b) => ntype s (binder_types s p ++ G) b
      | None => None
      end
  | None => None
  end.
Proof.
  simpl. destruct (ntype s G a) as [u |]; [| reflexivity].
  unfold pickn. induction arms as [| [p b] r IH]; simpl; [reflexivity |].
  destruct (holds s u p); [reflexivity | exact IH].
Qed.

(**md ## Specialization

A specialization at an instantiation is a term of RFC 0001 with no match and no type. Each match
is replaced by the body of the arm selected, with the scrutinee bound once for each binder of the
arm.
*)

(** A body with the innermost variable bound again a number of times.
    - [k:] the number of further bindings.
    - [b:] the body. *)
Fixpoint binds (k : nat) (b : mtm) : mtm :=
  match k with
  | 0 => b
  | S k => MLet (MVar 0) (binds k b)
  end.

(** The specialization of a body at an instantiation, or [None] when some match has no arm or
    some scrutinee has no type.
    - [s:] the instantiation.
    - [G:] the types of the variables in scope, which decide the arm of each match.
    - [e:] the body. *)
Fixpoint nspec (s : inst3) (G : list ty) (e : ntm) : option mtm :=
  match e with
  | NVar n => Some (MVar n)
  | NPrim o a => option_map (MPrim o) (nspec s G a)
  | NPair a b =>
      match nspec s G a, nspec s G b with
      | Some x, Some y => Some (MPair x y)
      | _, _ => None
      end
  | NFst a => option_map MFst (nspec s G a)
  | NSnd a => option_map MSnd (nspec s G a)
  | NLet a b =>
      match ntype s G a, nspec s G a with
      | Some x, Some ma => option_map (MLet ma) (nspec s (x :: G) b)
      | _, _ => None
      end
  | NMatch a arms =>
      match ntype s G a, nspec s G a with
      | Some u, Some ma =>
          (fix go (l : list (test * ntm)) : option mtm :=
             match l with
             | [] => None
             | (p, b) :: r =>
                 if holds s u p
                 then option_map (fun mb => MLet ma (binds (pred (arity p)) mb))
                        (nspec s (binder_types s p ++ G) b)
                 else go r
             end) arms
      | _, _ => None
      end
  end.

(** Specializing a match is specializing the body of the arm selected. *)
Lemma nspec_match (s : inst3) (G : list ty) (a : ntm) (arms : list (test * ntm)) :
  nspec s G (NMatch a arms) =
  match ntype s G a, nspec s G a with
  | Some u, Some ma =>
      match pickn s u arms with
      | Some (p, b) =>
          option_map (fun mb => MLet ma (binds (pred (arity p)) mb))
            (nspec s (binder_types s p ++ G) b)
      | None => None
      end
  | _, _ => None
  end.
Proof.
  simpl. destruct (ntype s G a) as [u |]; [| reflexivity].
  destruct (nspec s G a) as [ma |]; [| reflexivity].
  unfold pickn. induction arms as [| [p b] r IH]; simpl; [reflexivity |].
  destruct (holds s u p); [reflexivity | exact IH].
Qed.

(** Binding the innermost variable again does not change the type of the body. *)
Lemma mtype_binds (k : nat) (b : mtm) :
  forall (u : ty) (G : list ty),
    mtype (u :: G) (binds k b) = mtype (repeat u k ++ u :: G) b.
Proof.
  induction k as [| k IH]; intros u G; simpl; [reflexivity |].
  rewrite IH, repeat_shift. reflexivity.
Qed.

(** Binding the innermost variable again binds its value again. *)
Lemma eval_binds (k : nat) (b : mtm) :
  forall (v : val) (env : list val),
    eval (v :: env) (binds k b) = eval (repeat v k ++ v :: env) b.
Proof.
  induction k as [| k IH]; intros v env; simpl; [reflexivity |].
  rewrite IH, repeat_shift. reflexivity.
Qed.

(**md ## What a body means

The reference meaning is given with the instantiation and the types of the variables at hand.
Evaluating a match looks at the type of its scrutinee and takes the arm selected. This is how a
compiler that carried types at run time would run the body. It is the specification of behaviour,
not the implementation.
*)

(** The value of a body at an instantiation, or [None] where evaluation is stuck.
    - [s:] the instantiation, which a match inspects.
    - [G:] the types of the variables in scope, which a match inspects.
    - [env:] the values of the variables in scope, innermost first.
    - [e:] the body. *)
Fixpoint nseval (s : inst3) (G : list ty) (env : list val) (e : ntm) : option val :=
  match e with
  | NVar n => nth_error env n
  | NPrim o a =>
      match nseval s G env a with
      | Some v => apply o v
      | None => None
      end
  | NPair a b =>
      match nseval s G env a, nseval s G env b with
      | Some x, Some y => Some (VPair x y)
      | _, _ => None
      end
  | NFst a =>
      match nseval s G env a with
      | Some (VPair x _) => Some x
      | _ => None
      end
  | NSnd a =>
      match nseval s G env a with
      | Some (VPair _ y) => Some y
      | _ => None
      end
  | NLet a b =>
      match ntype s G a, nseval s G env a with
      | Some x, Some v => nseval s (x :: G) (v :: env) b
      | _, _ => None
      end
  | NMatch a arms =>
      match ntype s G a, nseval s G env a with
      | Some u, Some v =>
          (fix go (l : list (test * ntm)) : option val :=
             match l with
             | [] => None
             | (p, b) :: r =>
                 if holds s u p
                 then nseval s (binder_types s p ++ G) (repeat v (arity p) ++ env) b
                 else go r
             end) arms
      | _, _ => None
      end
  end.

(** Evaluating a match is evaluating the body of the arm selected, with the scrutinee bound to
    each of the arm's binders. *)
Lemma nseval_match
    (s : inst3) (G : list ty) (env : list val) (a : ntm) (arms : list (test * ntm)) :
  nseval s G env (NMatch a arms) =
  match ntype s G a, nseval s G env a with
  | Some u, Some v =>
      match pickn s u arms with
      | Some (p, b) => nseval s (binder_types s p ++ G) (repeat v (arity p) ++ env) b
      | None => None
      end
  | _, _ => None
  end.
Proof.
  simpl. destruct (ntype s G a) as [u |]; [| reflexivity].
  destruct (nseval s G env a) as [v |]; [| reflexivity].
  unfold pickn. induction arms as [| [p b] r IH]; simpl; [reflexivity |].
  destruct (holds s u p); [reflexivity | exact IH].
Qed.

(**md ## Erasure and safety *)

(**md
**A nested type-case is erased: the specialization computes what the body means.**

Whenever a body specializes at an instantiation, the specialization returns exactly what the
reference meaning returns there, on every input. The reference meaning inspects the instantiation
and the type of every scrutinee. The specialization has no access to either. So a type-case over
several variables, nested to any depth, needs no run-time test, tag or type argument.

This is RFC 0001's `specialization_preserves_meaning` for several variables and nested matches.
The proof is by induction on the body and uses no assumption.

- [s:] the instantiation.
- [e:] the body.
*)
Theorem nested_specialization_preserves_meaning (s : inst3) (e : ntm) :
  forall (G : list ty) (m : mtm), nspec s G e = Some m ->
  forall env : list val, nseval s G env e = eval env m.
Proof.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | a arms IHa IH]
    using ntm_arms_ind; intros G m H env.
  - simpl in H. injection H as <-. reflexivity.
  - simpl in H. destruct (nspec s G e) as [x |] eqn:Hx; [| discriminate].
    simpl in H. injection H as <-. simpl. rewrite (IH G x Hx env). reflexivity.
  - simpl in H. destruct (nspec s G a) as [x |] eqn:Hx; [| discriminate].
    destruct (nspec s G b) as [y |] eqn:Hy; [| discriminate].
    injection H as <-. simpl. rewrite (IHa G x Hx env), (IHb G y Hy env). reflexivity.
  - simpl in H. destruct (nspec s G e) as [x |] eqn:Hx; [| discriminate].
    simpl in H. injection H as <-. simpl. rewrite (IH G x Hx env). reflexivity.
  - simpl in H. destruct (nspec s G e) as [x |] eqn:Hx; [| discriminate].
    simpl in H. injection H as <-. simpl. rewrite (IH G x Hx env). reflexivity.
  - simpl in H. destruct (ntype s G a) as [x |] eqn:Hx; [| discriminate].
    destruct (nspec s G a) as [ma |] eqn:Hma; [| discriminate].
    destruct (nspec s (x :: G) b) as [mb |] eqn:Hmb; [| discriminate].
    simpl in H. injection H as <-. simpl. rewrite Hx, (IHa G ma Hma env).
    destruct (eval env ma) as [v |]; [| reflexivity]. apply (IHb _ mb Hmb).
  - rewrite nspec_match in H. rewrite nseval_match.
    destruct (ntype s G a) as [u |] eqn:Hu; [| discriminate].
    destruct (nspec s G a) as [ma |] eqn:Hma; [| discriminate].
    destruct (pickn s u arms) as [[p b] |] eqn:Hp; [| discriminate].
    destruct (nspec s (binder_types s p ++ G) b) as [mb |] eqn:Hmb; [| discriminate].
    simpl in H. injection H as <-. rewrite (IHa G ma Hma env). cbn [eval].
    destruct (eval env ma) as [v |]; [| reflexivity].
    destruct (find_some _ _ Hp) as [Hin _]. rewrite Forall_forall in IH.
    rewrite (IH (p, b) Hin _ mb Hmb), eval_binds, binder_env. reflexivity.
Qed.

(**md
**A body that has a type specializes, and the specialization has that type.**

If a body is typed at an instantiation, its specialization exists and RFC 0001's checker gives it
the same type. No match is left without an arm, at any depth.

- [s:] the instantiation.
- [e:] the body.
*)
Theorem typed_body_specializes (s : inst3) (e : ntm) :
  forall (G : list ty) (r : ty), ntype s G e = Some r ->
  exists m, nspec s G e = Some m /\ mtype G m = Some r.
Proof.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | a arms IHa IH]
    using ntm_arms_ind; intros G r H.
  - exists (MVar n). split; [reflexivity | exact H].
  - simpl in H. destruct (ntype s G e) as [x |] eqn:Hx; [| discriminate].
    destruct (IH G x Hx) as [m [Hm Ht]]. exists (MPrim o m). split.
    + simpl. rewrite Hm. reflexivity.
    + simpl. rewrite Ht. exact H.
  - simpl in H. destruct (ntype s G a) as [x |] eqn:Hx; [| discriminate].
    destruct (ntype s G b) as [y |] eqn:Hy; [| discriminate]. injection H as <-.
    destruct (IHa G x Hx) as [ma [Hma Hta]]. destruct (IHb G y Hy) as [mb [Hmb Htb]].
    exists (MPair ma mb). split.
    + simpl. rewrite Hma, Hmb. reflexivity.
    + simpl. rewrite Hta, Htb. reflexivity.
  - simpl in H. destruct (ntype s G e) as [x |] eqn:Hx; [| discriminate].
    destruct (IH G x Hx) as [m [Hm Ht]]. exists (MFst m). split.
    + simpl. rewrite Hm. reflexivity.
    + simpl. rewrite Ht. exact H.
  - simpl in H. destruct (ntype s G e) as [x |] eqn:Hx; [| discriminate].
    destruct (IH G x Hx) as [m [Hm Ht]]. exists (MSnd m). split.
    + simpl. rewrite Hm. reflexivity.
    + simpl. rewrite Ht. exact H.
  - simpl in H. destruct (ntype s G a) as [x |] eqn:Hx; [| discriminate].
    destruct (IHa G x Hx) as [ma [Hma Hta]]. destruct (IHb (x :: G) r H) as [mb [Hmb Htb]].
    exists (MLet ma mb). split.
    + simpl. rewrite Hx, Hma, Hmb. reflexivity.
    + simpl. rewrite Hta. exact Htb.
  - rewrite ntype_match in H.
    destruct (ntype s G a) as [u |] eqn:Hu; [| discriminate].
    destruct (pickn s u arms) as [[p b] |] eqn:Hp; [| discriminate].
    destruct (IHa G u Hu) as [ma [Hma Hta]].
    destruct (find_some _ _ Hp) as [Hin Hh]. simpl in Hh. rewrite Forall_forall in IH.
    destruct (IH (p, b) Hin _ r H) as [mb [Hmb Htb]]. simpl in Hmb.
    exists (MLet ma (binds (pred (arity p)) mb)). split.
    + rewrite nspec_match, Hu, Hma, Hp, Hmb. reflexivity.
    + simpl. rewrite Hta, mtype_binds, <- (binder_ctx s u p G Hh). exact Htb.
Qed.

(** The check of a definition, as the compiler computes it at the definition: at every
    instantiation in the table, the body has the declared result type. The scrutinee is variable
    zero of the body.
    - [G:] the types of the other parameters.
    - [e:] the body.
    - [res:] the declared result type. *)
Definition ncheck (CA CB : cset) (G : list oty3) (e : ntm) (res : oty3) : bool :=
  forallb
    (fun s =>
       match ntype s (iT s :: map (inst3ty s) G) e with
       | Some t => tyeqb t (inst3ty s res)
       | None => false
       end)
    (table CA CB).

(**md
**A definition with nested matches that checks runs to a value at every instantiation.**

Take a definition whose check passes, any instantiation that satisfies the constraints, a
scrutinee of the type `'T` is instantiated to, and arguments of the parameter types. The
definition returns a value of the declared result type. No inner match is left without an arm at
an instantiation that can occur, and no arm uses a binder at a type its value does not have.

This is `checked_match_runs` with matches allowed anywhere in a body. It rests on the same
assumption, that every witness is implemented at its declared type.

- [G:] the types of the other parameters.
- [e:] the body.
- [res:] the declared result type.
- [x:] the scrutinee.
*)
Theorem checked_nested_runs
  (CA CB : cset) (G : list oty3) (e : ntm) (res : oty3)
  (s : inst3) (env : list val) (x : val) :
  ncheck CA CB G e res = true ->
  valid CA CB s -> has_ty x (iT s) ->
  Forall2 has_ty env (map (inst3ty s) G) ->
  exists v, nseval s (iT s :: map (inst3ty s) G) (x :: env) e = Some v /\
            has_ty v (inst3ty s res).
Proof.
  intros C V Hx HE. unfold ncheck in C. rewrite forallb_forall in C.
  specialize (C s (proj2 (table_iff_valid CA CB s) V)).
  destruct (ntype s (iT s :: map (inst3ty s) G) e) as [t |] eqn:T; [| discriminate].
  apply tyeqb_iff in C. subst t.
  destruct (typed_body_specializes s e _ _ T) as [m [Hm Ht]].
  rewrite (nested_specialization_preserves_meaning s e _ m Hm).
  apply (specialization_is_safe m (iT s :: map (inst3ty s) G) (x :: env) _);
    [constructor; assumption | exact Ht].
Qed.

(**md ## What an inner match knows

An arm's body is typed and run only at instantiations where the arm's test succeeds. An inner
match therefore sits in the region of every arm around it, and the equations of those regions are
in scope. Three statements make this precise.
*)

(** Selecting among the arms that match selects the same arm. *)
Lemma find_filter {A : Type} (f : A -> bool) (l : list A) :
  find f (filter f l) = find f l.
Proof.
  induction l as [| a l IH]; simpl; [reflexivity |].
  destruct (f a) eqn:E; simpl; [rewrite E; reflexivity | exact IH].
Qed.

(**md
**An arm is checked and run only where its test succeeds.**

At an instantiation, a match has the type and the value of the same match with every arm removed
whose test fails there. The body of an arm that does not match is never typed at that
instantiation, so it may be ill typed there. This is what lets a body rely on the equation its
test establishes, and on the equations of the arms around it.

- [e:] the scrutinee.
- [u:] the type of the scrutinee at the instantiation.
*)
Theorem arm_checked_where_it_matches
    (s : inst3) (G : list ty) (e : ntm) (arms : list (test * ntm)) (u : ty) :
  ntype s G e = Some u ->
  let live := filter (fun a => holds s u (fst a)) arms in
  ntype s G (NMatch e arms) = ntype s G (NMatch e live) /\
  forall env : list val, nseval s G env (NMatch e arms) = nseval s G env (NMatch e live).
Proof.
  intros H live. subst live. split.
  - rewrite !ntype_match, H. unfold pickn. rewrite find_filter. reflexivity.
  - intros env. rewrite !nseval_match, H.
    destruct (nseval s G env e) as [v |]; [| reflexivity].
    unfold pickn. rewrite find_filter. reflexivity.
Qed.

(** A match with one arm. *)
Lemma ntype_one (s : inst3) (G : list ty) (e : ntm) (p : test) (b : ntm) :
  ntype s G (NMatch e [(p, b)]) =
  match ntype s G e with
  | Some u => if holds s u p then ntype s (binder_types s p ++ G) b else None
  | None => None
  end.
Proof.
  simpl. destruct (ntype s G e) as [u |]; [| reflexivity].
  destruct (holds s u p); reflexivity.
Qed.

Lemma nseval_one (s : inst3) (G : list ty) (env : list val) (e : ntm) (p : test) (b : ntm) :
  nseval s G env (NMatch e [(p, b)]) =
  match ntype s G e, nseval s G env e with
  | Some u, Some v =>
      if holds s u p
      then nseval s (binder_types s p ++ G) (repeat v (arity p) ++ env) b
      else None
  | _, _ => None
  end.
Proof.
  simpl. destruct (ntype s G e) as [u |]; [| reflexivity].
  destruct (nseval s G env e) as [v |]; [| reflexivity].
  destruct (holds s u p); reflexivity.
Qed.

(**md
**A conjunction of tests is a nested test.**

The arm `:? 'A & :? 'B -> b` and the arm `:? 'A as a -> (match a with :? 'B -> b)` have the same
type and the same value at every instantiation, for any two tests and any body. The inner test is
taken on the outer binder, which has the scrutinee's type because the outer test succeeded. So the
inner arm is reached exactly where both tests hold, which is the region of the conjunction. The
intersection arm of this RFC is the outer equation carried into an inner match.

The two forms differ when more arms follow. A conjunction that fails falls through to the next
arm. An inner match that fails has no arm, and the definition is rejected.

- [e:] the scrutinee.
- [p:] the outer test.
- [q:] the inner test.
- [b:] the body.
*)
Theorem conjunction_is_nesting
    (s : inst3) (G : list ty) (e : ntm) (p q : test) (b : ntm) :
  let flat := NMatch e [(Both p q, b)] in
  let nested := NMatch e [(p, NMatch (NVar 0) [(q, b)])] in
  ntype s G flat = ntype s G nested /\
  forall env : list val, nseval s G env flat = nseval s G env nested.
Proof.
  intros flat nested. subst flat nested. split.
  - rewrite !ntype_one. destruct (ntype s G e) as [u |]; [| reflexivity].
    cbn [holds]. destruct (holds s u p) eqn:Hp; cbn [andb]; [| reflexivity].
    cbn [ntype]. rewrite (binder_head s u p G Hp).
    destruct (holds s u q) eqn:Hq; [| reflexivity].
    cbn [binder_types]. rewrite (holds_binders s u p Hp), (holds_binders s u q Hq).
    rewrite !app_assoc, <- !repeat_app, (Nat.add_comm (arity q)). reflexivity.
  - intros env. rewrite !nseval_one. destruct (ntype s G e) as [u |]; [| reflexivity].
    destruct (nseval s G env e) as [v |]; [| reflexivity].
    cbn [holds]. destruct (holds s u p) eqn:Hp; cbn [andb]; [| reflexivity].
    cbn [ntype nseval]. rewrite (binder_head s u p G Hp), repeat_head.
    destruct (holds s u q) eqn:Hq; [| reflexivity].
    cbn [binder_types arity]. rewrite (holds_binders s u p Hp), (holds_binders s u q Hq).
    rewrite !app_assoc, <- !repeat_app, (Nat.add_comm (arity q)). reflexivity.
Qed.

(** The example of this module's introduction. The scrutinee `x` is variable zero and `y` is the
    other parameter. Inside the first arm, `y` is variable two. *)
Definition region_example : ntm :=
  NMatch (NVar 0) [(IsA, NMatch (NVar 2) [(IsA, NVar 0)]); (IsB, NVar 0)].

(** The inner match of the example, written as a definition on its own. Here `y` is variable
    one. *)
Definition inner_alone : ntm := NMatch (NVar 1) [(IsA, NVar 0)].

(**md
**An inner match is checked against its region, not against the whole table.**

The example definition checks for every pair of member sets. Its inner match has the single arm
`:? 'A`, on a scrutinee of type `'T`. That is exhaustive inside the outer arm `:? 'A`, because
`'T` is `'A` there, and the inner binder may be returned at the type `'T` for the same reason.

The same inner match written as a definition of its own is rejected for `'A : (x | y)` and
`'B : (y)`: at the instantiation where `'T` is `'B` and `'B` differs from `'A`, it has no arm. So
coverage of an inner match is relative to the arm it is in, and the outer equation is what the
check uses.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
*)
Theorem nested_match_checked_in_its_region :
  (forall CA CB : cset, ncheck CA CB [VT] region_example VT = true) /\
  (forall x y : ty, x <> y -> ncheck [x; y] [y] [VT] inner_alone VT = false).
Proof.
  split.
  - intros CA CB. unfold ncheck. apply forallb_forall. intros s Hs.
    apply table_iff_valid in Hs. destruct Hs as [_ [_ Ht]].
    unfold region_example. cbn [ntype nth_error holds binder_types app map inst3ty].
    destruct (tyeqb (iT s) (iA s)) eqn:EA.
    + apply tyeqb_iff in EA. apply tyeqb_iff. symmetry. exact EA.
    + destruct (tyeqb (iT s) (iB s)) eqn:EB.
      * apply tyeqb_iff in EB. apply tyeqb_iff. symmetry. exact EB.
      * apply tyeqb_neq in EA. apply tyeqb_neq in EB. destruct Ht; contradiction.
  - intros x y N.
    destruct (ncheck [x; y] [y] [VT] inner_alone VT) eqn:C; [| reflexivity]. exfalso.
    unfold ncheck in C. rewrite forallb_forall in C.
    assert (V : In (Inst x y y) (table [x; y] [y])).
    { apply table_iff_valid. unfold valid, sat. simpl. intuition. }
    specialize (C (Inst x y y) V). unfold inner_alone in C.
    assert (Q : tyeqb y x = false) by (apply tyeqb_false; congruence).
    cbn [ntype nth_error holds binder_types app map inst3ty iT iA iB] in C.
    rewrite Q in C. discriminate.
Qed.

(**md ## Agreement with Bodies

A match with no nesting is a definition of [Bodies](Clef.RFC0002.Bodies.html). The two models
agree on it. The only difference in form is that here the scrutinee stays in scope beside the
binders, so a body of Bodies is moved past one more variable.
*)

(** A specialized term moved past one more variable.
    - [k:] the number of variables bound inside the term's own context, which are kept.
    - [m:] the term. *)
Fixpoint mshift (k : nat) (m : mtm) : mtm :=
  match m with
  | MVar n => if n <? k then MVar n else MVar (S n)
  | MPrim o a => MPrim o (mshift k a)
  | MPair a b => MPair (mshift k a) (mshift k b)
  | MFst a => MFst (mshift k a)
  | MSnd a => MSnd (mshift k a)
  | MLet a b => MLet (mshift k a) (mshift (S k) b)
  end.

Lemma nth_error_insert {A : Type} (pre l : list A) (x : A) (n : nat) :
  nth_error (pre ++ x :: l) (if n <? length pre then n else S n) = nth_error (pre ++ l) n.
Proof.
  destruct (n <? length pre) eqn:E.
  - apply Nat.ltb_lt in E. rewrite !nth_error_app1 by exact E. reflexivity.
  - apply Nat.ltb_ge in E. rewrite !nth_error_app2 by lia.
    replace (S n - length pre) with (S (n - length pre)) by lia. reflexivity.
Qed.

(** Moving a term past a variable does not change its type. *)
Lemma mtype_shift (m : mtm) :
  forall (pre G : list ty) (x : ty),
    mtype (pre ++ x :: G) (mshift (length pre) m) = mtype (pre ++ G) m.
Proof.
  induction m as [n | o m IH | a IHa b IHb | m IH | m IH | a IHa b IHb]; intros pre G x; simpl.
  - pose proof (nth_error_insert pre G x n) as H.
    destruct (n <? length pre); exact H.
  - rewrite IH. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IHa. destruct (mtype (pre ++ G) a) as [t |]; [| reflexivity].
    apply (IHb (t :: pre) G x).
Qed.

(** Moving a term past a variable does not change its value. *)
Lemma eval_shift (m : mtm) :
  forall (pre env : list val) (x : val),
    eval (pre ++ x :: env) (mshift (length pre) m) = eval (pre ++ env) m.
Proof.
  induction m as [n | o m IH | a IHa b IHb | m IH | m IH | a IHa b IHb]; intros pre env x; simpl.
  - pose proof (nth_error_insert pre env x n) as H.
    destruct (n <? length pre); exact H.
  - rewrite IH. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IHa. destruct (eval (pre ++ env) a) as [v |]; [| reflexivity].
    apply (IHb (v :: pre) env x).
Qed.

(** A specialized term as a body with no match. *)
Fixpoint ofm (m : mtm) : ntm :=
  match m with
  | MVar n => NVar n
  | MPrim o a => NPrim o (ofm a)
  | MPair a b => NPair (ofm a) (ofm b)
  | MFst a => NFst (ofm a)
  | MSnd a => NSnd (ofm a)
  | MLet a b => NLet (ofm a) (ofm b)
  end.

(** A body with no match has the type RFC 0001's checker gives it. *)
Lemma ntype_ofm (m : mtm) : forall (s : inst3) (G : list ty), ntype s G (ofm m) = mtype G m.
Proof.
  induction m as [n | o m IH | a IHa b IHb | m IH | m IH | a IHa b IHb]; intros s G; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IHa. destruct (mtype G a) as [t |]; [apply IHb | reflexivity].
Qed.

(** A typed body with no match has the value RFC 0001 gives it. *)
Lemma nseval_ofm (m : mtm) :
  forall (s : inst3) (G : list ty) (env : list val) (t : ty),
    mtype G m = Some t -> nseval s G env (ofm m) = eval env m.
Proof.
  induction m as [n | o m IH | a IHa b IHb | m IH | m IH | a IHa b IHb];
    intros s G env t H; simpl in H; simpl.
  - reflexivity.
  - destruct (mtype G m) as [x |] eqn:Hx; [| discriminate].
    rewrite (IH s G env x); [reflexivity | first [exact Hx | reflexivity]].
  - destruct (mtype G a) as [x |] eqn:Hx; [| discriminate].
    destruct (mtype G b) as [y |] eqn:Hy; [| discriminate].
    rewrite (IHa s G env x), (IHb s G env y); first [reflexivity | assumption].
  - destruct (mtype G m) as [x |] eqn:Hx; [| discriminate].
    rewrite (IH s G env x); [reflexivity | first [exact Hx | reflexivity]].
  - destruct (mtype G m) as [x |] eqn:Hx; [| discriminate].
    rewrite (IH s G env x); [reflexivity | first [exact Hx | reflexivity]].
  - destruct (mtype G a) as [x |] eqn:Hx; [| discriminate].
    rewrite ntype_ofm, Hx, (IHa s G env x); [| first [exact Hx | reflexivity]].
    destruct (eval env a) as [v |]; [| reflexivity].
    apply (IHb s (x :: G) (v :: env) t H).
Qed.

(** An arm of Bodies as an arm of a match on variable zero. *)
Definition as_arm (a : arm) : test * ntm :=
  (atest a, ofm (mshift (arity (atest a)) (abody a))).

(** A definition of Bodies as a body here: one match on the scrutinee, with no nesting. *)
Definition flat (arms : list arm) : ntm := NMatch (NVar 0) (map as_arm arms).

Lemma find_ext {A : Type} (f g : A -> bool) (l : list A) :
  (forall a, f a = g a) -> find f l = find g l.
Proof.
  intros H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

(** The match selects the arm Bodies selects. *)
Lemma pickn_flat (CA CB : cset) (s : inst3) (arms : list arm) :
  pickn s (iT s) (map as_arm arms) = option_map as_arm (selecta Equation CA CB arms s).
Proof.
  unfold pickn, selecta. rewrite find_map. f_equal. apply find_ext.
  intros a. unfold amatches. apply holds_scrutinee.
Qed.

(** The type of the match is the type of the body of the arm Bodies selects. *)
Lemma ntype_flat (CA CB : cset) (s : inst3) (G : list ty) (arms : list arm) :
  ntype s (iT s :: G) (flat arms) =
  match selecta Equation CA CB arms s with
  | Some a => mtype (binder_types s (atest a) ++ G) (abody a)
  | None => None
  end.
Proof.
  unfold flat. rewrite ntype_match. cbn [ntype nth_error]. rewrite (pickn_flat CA CB).
  destruct (selecta Equation CA CB arms s) as [a |]; [| reflexivity].
  cbn [option_map as_arm]. rewrite ntype_ofm.
  pose proof (mtype_shift (abody a) (binder_types s (atest a)) G (iT s)) as E.
  rewrite binder_length in E. exact E.
Qed.

(**md
**A definition that Bodies accepts is accepted here, and computes the same result.**

Take a definition with no nested match whose check passes in Bodies under the equation reading.
Written as a single match on the scrutinee, it passes the check of this module, and at every
instantiation that satisfies the constraints it returns what Bodies says it returns. The model of
nested matches extends the model of Bodies and does not replace it.

The converse does not hold for the check. Bodies types every arm that matches at an
instantiation, and this module types the one selected.

- [G:] the types of the other parameters.
- [arms:] the arms of the definition.
- [res:] the declared result type.
*)
Theorem nested_extends_bodies
    (CA CB : cset) (G : list oty3) (arms : list arm) (res : oty3) :
  check3 Equation CA CB G arms res = true ->
  ncheck CA CB G (flat arms) res = true /\
  forall (s : inst3) (env : list val) (x : val),
    valid CA CB s ->
    nseval s (iT s :: map (inst3ty s) G) (x :: env) (flat arms) =
    run Equation CA CB arms s env x.
Proof.
  intros C. unfold check3 in C. rewrite forallb_forall in C.
  assert (K : forall s, In s (table CA CB) ->
            exists a, selecta Equation CA CB arms s = Some a /\
              mtype (binder_types s (atest a) ++ map (inst3ty s) G) (abody a) =
              Some (inst3ty s res)).
  { intros s Hs. specialize (C s Hs). apply andb_true_iff in C. destruct C as [C1 C2].
    destruct (existsb_find _ _ C1) as [a F]. exists a. split; [exact F |].
    destruct (find_some _ _ F) as [Ia Ma].
    rewrite forallb_forall in C2. specialize (C2 a Ia). rewrite Ma in C2. simpl in C2.
    unfold arm_ok in C2.
    destruct (mtype (binder_types s (atest a) ++ map (inst3ty s) G) (abody a)) as [t |];
      [| discriminate].
    apply tyeqb_iff in C2. subst t. reflexivity. }
  split.
  - unfold ncheck. apply forallb_forall. intros s Hs.
    destruct (K s Hs) as [a [F T]].
    rewrite (ntype_flat CA CB), F, T. apply tyeqb_refl.
  - intros s env x V.
    destruct (K s (proj2 (table_iff_valid CA CB s) V)) as [a [F T]].
    unfold flat, run. rewrite nseval_match. cbn [ntype nseval nth_error].
    rewrite (pickn_flat CA CB), F. cbn [option_map as_arm].
    pose proof (mtype_shift (abody a) (binder_types s (atest a)) (map (inst3ty s) G) (iT s))
      as Et.
    rewrite binder_length, T in Et.
    rewrite (nseval_ofm _ s _ _ _ Et).
    pose proof (eval_shift (abody a) (repeat x (arity (atest a))) env x) as Ev.
    rewrite repeat_length in Ev. exact Ev.
Qed.

(**md ## Rules stated in prose

These parts of a nested type-case are not modelled.

1. **Arm order in an inner match.** The overlap check and the two ways of gluing are stated in
   Regions and Bodies for a match on the parameter of type `'T`, over the whole table. An inner
   match sees part of the table and may scrutinise a term of another type. The check for it would
   compare arms over the region of the enclosing arms. That check is not defined here.
2. **Every matching arm.** This module types the arm selected at each instantiation. Bodies types
   every arm that matches, which is what lets arms be reordered. The stronger check for nested
   matches is not defined here.
3. **Unreachable inner arms.** An inner arm whose test fails throughout its region can never run.
   The model accepts it. A compiler would report it, as it reports an unreachable rule.
*)
