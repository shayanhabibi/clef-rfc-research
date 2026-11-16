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

Nine questions are answered.

1. Is a nested type-case still erased? A specialization has no type to inspect, at any depth.
2. Is a definition that checks still safe to run at every instantiation?
3. What does an inner match know about the arm it is in?
4. Does the model agree with [Bodies](Clef.RFC0002.Bodies.html) where there is no nesting?
5. Over which instantiations are the arms of an inner match compared by the overlap check?
6. How is that set of instantiations computed from a body?
7. May two overlapping arms of an inner match be written in either order when their bodies agree?
8. How do the overlap check and the gluing condition of a whole body relate?
9. Which arms can never be selected, and how does reporting them relate to the checks?

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
safety. Arm order in an inner match is taken up in its own section below.
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

(**md ## Arm order in an inner match

The overlap check of [Regions](Clef.RFC0002.Regions.html) is stated for the match on the
parameter of type `'T`, and it compares arms over the whole table. An inner match differs in two
ways. Its scrutinee may be any term, so its type varies with the instantiation. And it runs only
at the instantiations that reach it. This section states the check for any set of instantiations
and any scrutinee, and asks which set an inner match should be checked over.
*)

(** One test is at least as specific as another over a set of instantiations when it succeeds
    there only where the other does.
    - [R:] the instantiations considered.
    - [u:] the type of the scrutinee at each instantiation.
    - [p:] the more specific test.
    - [q:] the more general test. *)
Definition le_in (R : list inst3) (u : inst3 -> ty) (p q : test) : bool :=
  forallb (fun s => implb (holds s (u s) p) (holds s (u s) q)) R.

(** The computed comparison agrees with its meaning. *)
Lemma le_in_iff (R : list inst3) (u : inst3 -> ty) (p q : test) :
  le_in R u p q = true <->
  forall s, In s R -> holds s (u s) p = true -> holds s (u s) q = true.
Proof.
  unfold le_in. rewrite forallb_forall. split; intros H s Hs.
  - intro M. specialize (H s Hs). cbn beta in H. rewrite M in H. exact H.
  - cbn beta. destruct (holds s (u s) p) eqn:M; [| reflexivity]. apply (H s Hs M).
Qed.

Lemma le_in_refl (R : list inst3) (u : inst3 -> ty) (p : test) : le_in R u p p = true.
Proof.
  apply le_in_iff. intros s _ M. exact M.
Qed.

(** The overlap check over a set of instantiations. For each arm, and each instantiation in the
    set its test succeeds at, the first earlier arm that also succeeds there must be at least as
    specific as this one over the set.
    - [R:] the instantiations considered.
    - [u:] the type of the scrutinee at each instantiation.
    - [seen:] the arms before the ones being checked, in source order.
    - [arms:] the arms still to check. *)
Fixpoint ordered_in (R : list inst3) (u : inst3 -> ty) (seen arms : list test) : bool :=
  match arms with
  | [] => true
  | q :: rest =>
      forallb
        (fun s =>
           implb (holds s (u s) q)
             (match find (fun p => holds s (u s) p) seen with
              | None => true
              | Some p => le_in R u p q
              end))
        R
      && ordered_in R u (seen ++ [q]) rest
  end.

Lemma forallb_eq {A : Type} (f g : A -> bool) (l : list A) :
  (forall a, f a = g a) -> forallb f l = forallb g l.
Proof.
  intros H. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite H, IH. reflexivity.
Qed.

(** Over the whole table, on the parameter of type `'T`, the comparison is that of Regions. *)
Lemma le_in_table (CA CB : cset) (p q : test) :
  le_in (table CA CB) iT p q = le Equation CA CB p q.
Proof.
  unfold le_in, le. apply forallb_eq. intros s.
  rewrite !(holds_scrutinee CA CB). reflexivity.
Qed.

(**md
**The overlap check of Regions is this check over the whole table.**

On the parameter of type `'T`, over every instantiation, the check stated here is the overlap
check of Regions under the equation reading. So the theorems of this section are about the same
check, taken over a smaller set and on another scrutinee.

- [seen:] the arms before the ones being checked.
- [arms:] the arms still to check.
*)
Theorem ordered_in_table (CA CB : cset) (arms : list test) :
  forall seen : list test,
    ordered_in (table CA CB) iT seen arms = ordered Equation CA CB seen arms.
Proof.
  induction arms as [| q rest IH]; intros seen; cbn [ordered_in ordered]; [reflexivity |].
  rewrite IH. f_equal. apply forallb_eq. intros s.
  rewrite (holds_scrutinee CA CB).
  rewrite (find_ext (fun p => holds s (iT s) p) (matches Equation CA CB s) seen)
    by (intros a; apply holds_scrutinee).
  destruct (find (matches Equation CA CB s) seen) as [p |]; [| reflexivity].
  rewrite le_in_table. reflexivity.
Qed.

(** The overlap check, for arms that follow a prefix already checked. *)
Lemma ordered_in_most_specific (R : list inst3) (u : inst3 -> ty) (arms : list test) :
  forall (seen : list test) (s : inst3) (p q : test),
    ordered_in R u seen arms = true ->
    In s R ->
    find (fun t => holds s (u s) t) (seen ++ arms) = Some p ->
    In q arms -> holds s (u s) q = true ->
    le_in R u p q = true.
Proof.
  induction arms as [| a rest IH]; intros seen s p q O V F Hq M; [destruct Hq |].
  cbn [ordered_in] in O. apply andb_true_iff in O. destruct O as [O1 O2].
  destruct Hq as [-> | Hq].
  - rewrite forallb_forall in O1. specialize (O1 s V). cbn beta in O1.
    rewrite M in O1. simpl in O1. rewrite find_app in F.
    destruct (find (fun t => holds s (u s) t) seen) as [p' |] eqn:Fs.
    + injection F as <-. exact O1.
    + simpl in F. rewrite M in F. injection F as <-. apply le_in_refl.
  - apply (IH (seen ++ [a]) s p q O2 V); [| exact Hq | exact M].
    rewrite <- app_assoc. exact F.
Qed.

(**md
**Under the check over a set, the first matching arm is the most specific one there.**

If a list of arms passes the check over a set of instantiations, then at every instantiation in
the set the arm selected by source order is at least as specific, over the set, as every other
arm whose test succeeds. This is `first_match_is_most_specific` for any scrutinee and any set.

- [R:] the instantiations considered.
- [u:] the type of the scrutinee at each instantiation.
- [p:] the test selected.
- [q:] any other test that succeeds.
*)
Theorem inner_first_match_is_most_specific
    (R : list inst3) (u : inst3 -> ty) (arms : list test) (s : inst3) (p q : test) :
  ordered_in R u [] arms = true ->
  In s R ->
  find (fun t => holds s (u s) t) arms = Some p ->
  In q arms -> holds s (u s) q = true ->
  le_in R u p q = true.
Proof.
  intros O V F. exact (ordered_in_most_specific R u arms [] s p q O V F).
Qed.

(**md
**A match accepted over a set is accepted over every smaller set.**

The check over the whole table is the stricter one. A list of arms that passes it passes the
check over any region. So checking an inner match over the whole table is sound. The question is
what it rejects without need.

- [R:] the smaller set.
- [R':] the larger set.
*)
Theorem check_over_larger_set_is_stricter
    (R R' : list inst3) (u : inst3 -> ty) (arms : list test) :
  incl R R' ->
  forall seen : list test,
    ordered_in R' u seen arms = true -> ordered_in R u seen arms = true.
Proof.
  intros I. induction arms as [| q rest IH]; intros seen O; [reflexivity |].
  cbn [ordered_in] in O. cbn [ordered_in].
  apply andb_true_iff in O. destruct O as [O1 O2].
  apply andb_true_iff. split; [| apply IH; exact O2].
  rewrite forallb_forall in O1. apply forallb_forall. intros s Hs.
  specialize (O1 s (I s Hs)). cbn beta in O1.
  destruct (holds s (u s) q); [| reflexivity]. simpl in O1. simpl.
  destruct (find (fun p => holds s (u s) p) seen) as [p |]; [| reflexivity].
  apply le_in_iff. intros s' Hs'.
  apply (proj1 (le_in_iff R' u p q) O1 s' (I s' Hs')).
Qed.

(** The instantiations of a set at which a test succeeds: the region of an arm that is written
    first.
    - [R:] the instantiations the match runs at.
    - [u:] the type of its scrutinee at each instantiation.
    - [p:] the test of the arm. *)
Definition restrict (R : list inst3) (u : inst3 -> ty) (p : test) : list inst3 :=
  filter (fun s => holds s (u s) p) R.

(**md
**The check over the region accepts an inner match the check over the table rejects.**

Take an inner match on a scrutinee of type `'T`, inside an arm `:? 'A` that is written first, with
the arms `:? 'B` then `:? 'A`. Over the region of the outer arm the check accepts it for every
pair of member sets. In that region `'T` is `'A`, so `:? 'A` succeeds everywhere and `:? 'B`,
which succeeds where the two variables are the same type, is the more specific arm and is rightly
first. Over the whole table the same two arms are rejected for `'A : (x | y)` and `'B : (y)`,
because outside the region `:? 'B` succeeds where `:? 'A` does not.

So the two candidate checks differ, and the one over the whole table rejects a match whose arms
are correctly ordered where it runs.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
*)
Theorem region_check_accepts_what_table_check_rejects :
  (forall CA CB : cset,
     ordered_in (restrict (table CA CB) iT IsA) iT [] [IsB; IsA] = true) /\
  (forall x y : ty, x <> y -> ordered_in (table [x; y] [y]) iT [] [IsB; IsA] = false).
Proof.
  split.
  - intros CA CB. cbn [ordered_in app].
    apply andb_true_iff. split; [| apply andb_true_iff; split; [| reflexivity]];
      apply forallb_forall; intros s Hs; cbn [find].
    + destruct (holds s (iT s) IsB); reflexivity.
    + destruct (holds s (iT s) IsA); [| reflexivity]. cbn [implb].
      destruct (holds s (iT s) IsB); [| reflexivity].
      apply le_in_iff. intros s' Hs' _. unfold restrict in Hs'.
      apply filter_In in Hs'. exact (proj2 Hs').
  - intros x y N. rewrite ordered_in_table.
    destruct (ordered Equation [x; y] [y] [] [IsB; IsA]) eqn:O; [| reflexivity]. exfalso.
    assert (V1 : valid [x; y] [y] (Inst y y y)) by (unfold valid, sat; simpl; intuition).
    assert (V2 : valid [x; y] [y] (Inst x y y)) by (unfold valid, sat; simpl; intuition).
    assert (L : le Equation [x; y] [y] IsB IsA = true).
    { apply (first_match_is_most_specific Equation [x; y] [y] [IsB; IsA] (Inst y y y) IsB IsA O V1).
      - unfold select. cbn [find matches iT iB]. rewrite tyeqb_refl. reflexivity.
      - simpl. auto.
      - cbn [matches iT iA]. apply tyeqb_refl. }
    apply N. symmetry. apply tyeqb_iff.
    exact (proj1 (le_iff Equation [x; y] [y] IsB IsA) L (Inst x y y) V2 (tyeqb_refl y)).
Qed.

(** Under the check over a set, with no two arms equally specific there, two lists holding the
    same arms select the same arm at every instantiation in the set. *)
Lemma inner_selection_order_free
    (R : list inst3) (u : inst3 -> ty) (l1 l2 : list (test * ntm)) :
  ordered_in R u [] (map fst l1) = true ->
  ordered_in R u [] (map fst l2) = true ->
  (forall a, In a l1 <-> In a l2) ->
  (forall a b, In a l1 -> In b l1 ->
     le_in R u (fst a) (fst b) = true -> le_in R u (fst b) (fst a) = true -> a = b) ->
  forall s, In s R -> pickn s (u s) l1 = pickn s (u s) l2.
Proof.
  intros O1 O2 P D s Hs.
  destruct (pickn s (u s) l1) as [a1 |] eqn:F1; destruct (pickn s (u s) l2) as [a2 |] eqn:F2.
  - destruct (find_some _ _ F1) as [I1 M1]. destruct (find_some _ _ F2) as [I2 M2].
    f_equal. apply (D a1 a2 I1 (proj2 (P a2) I2)).
    + apply (inner_first_match_is_most_specific R u (map fst l1) s (fst a1) (fst a2) O1 Hs).
      * rewrite find_map. unfold pickn in F1. rewrite F1. reflexivity.
      * apply in_map. apply P. exact I2.
      * exact M2.
    + apply (inner_first_match_is_most_specific R u (map fst l2) s (fst a2) (fst a1) O2 Hs).
      * rewrite find_map. unfold pickn in F2. rewrite F2. reflexivity.
      * apply in_map. apply P. exact I1.
      * exact M1.
  - destruct (find_some _ _ F1) as [I1 M1].
    pose proof (find_none _ _ F2 a1 (proj1 (P a1) I1)) as E. cbn beta in E.
    rewrite M1 in E. discriminate.
  - destruct (find_some _ _ F2) as [I2 M2].
    pose proof (find_none _ _ F1 a2 (proj2 (P a2) I2)) as E. cbn beta in E.
    rewrite M2 in E. discriminate.
  - reflexivity.
Qed.

(**md
**Under the check over its region, the order of an inner match's arms changes nothing.**

Take two lists holding the same arms. Both pass the overlap check over a set of instantiations,
and no two different arms are equally specific over that set. At every instantiation in the set
where the scrutinee has the stated type, the two matches select the same arm. So they have the
same type and return the same value.

The set is any set that holds every instantiation the match runs at. The region of the enclosing
arms is such a set, and so is the whole table. This is `priority_glues` and
`glued_order_irrelevant` for an inner match, and the conclusion is stronger: the same arm is
selected, where those theorems say only that the results are equal.

- [R:] the instantiations the match is checked over.
- [u:] the type of the scrutinee at each of them.
- [l1:] the arms in one order.
- [l2:] the same arms in another order.
- [e:] the scrutinee.
*)
Theorem inner_order_is_irrelevant
    (R : list inst3) (u : inst3 -> ty) (l1 l2 : list (test * ntm))
    (s : inst3) (G : list ty) (e : ntm) :
  ordered_in R u [] (map fst l1) = true ->
  ordered_in R u [] (map fst l2) = true ->
  (forall a, In a l1 <-> In a l2) ->
  (forall a b, In a l1 -> In b l1 ->
     le_in R u (fst a) (fst b) = true -> le_in R u (fst b) (fst a) = true -> a = b) ->
  In s R -> ntype s G e = Some (u s) ->
  ntype s G (NMatch e l1) = ntype s G (NMatch e l2) /\
  forall env : list val, nseval s G env (NMatch e l1) = nseval s G env (NMatch e l2).
Proof.
  intros O1 O2 P D Hs H.
  pose proof (inner_selection_order_free R u l1 l2 O1 O2 P D s Hs) as E. split.
  - rewrite !ntype_match, H, E. reflexivity.
  - intros env. rewrite !nseval_match, H, E. reflexivity.
Qed.

(**md ### Inner tests on a variable are decided by the region

The three-arm match splits the table by which of the three variables are equal. That leaves an
inner match little to decide.
*)

(** Whether an open type is one of the three variables. *)
Definition is_var (o : oty3) : Prop :=
  match o with
  | VA | VB | VT => True
  | _ => False
  end.

Lemma tyeqb_sym (x y : ty) : tyeqb x y = tyeqb y x.
Proof.
  destruct (tyeqb x y) eqn:E; symmetry.
  - apply tyeqb_iff. apply tyeqb_iff in E. congruence.
  - apply tyeqb_false. apply tyeqb_neq in E. congruence.
Qed.

(** At a valid instantiation the scrutinee's type is one of the two variables. *)
Lemma valid_cases (CA CB : cset) (s : inst3) :
  valid CA CB s -> tyeqb (iT s) (iA s) = true \/ tyeqb (iT s) (iB s) = true.
Proof.
  intros [_ [_ [H | H]]]; [left | right]; apply tyeqb_iff; exact H.
Qed.

(** Whether the two constrained variables are equal follows from the two tests on `'T`. *)
Lemma ab_decided (s : inst3) :
  tyeqb (iT s) (iA s) = true \/ tyeqb (iT s) (iB s) = true ->
  tyeqb (iA s) (iB s) = tyeqb (iT s) (iA s) && tyeqb (iT s) (iB s).
Proof.
  intros H.
  destruct (tyeqb (iT s) (iA s)) eqn:EA; destruct (tyeqb (iT s) (iB s)) eqn:EB; simpl.
  - apply tyeqb_iff. apply tyeqb_iff in EA. apply tyeqb_iff in EB. congruence.
  - apply tyeqb_false. apply tyeqb_iff in EA. apply tyeqb_neq in EB. congruence.
  - apply tyeqb_false. apply tyeqb_neq in EA. apply tyeqb_iff in EB. congruence.
  - destruct H; discriminate.
Qed.

(** A test on a scrutinee whose type is a variable depends only on which variables are equal. *)
Lemma var_test_by_equations (s1 s2 : inst3) (o : oty3) :
  is_var o ->
  tyeqb (iT s1) (iA s1) = tyeqb (iT s2) (iA s2) ->
  tyeqb (iT s1) (iB s1) = tyeqb (iT s2) (iB s2) ->
  tyeqb (iA s1) (iB s1) = tyeqb (iA s2) (iB s2) ->
  forall p, holds s1 (inst3ty s1 o) p = holds s2 (inst3ty s2 o) p.
Proof.
  intros Ho E1 E2 E3 p. induction p as [| | p1 IH1 p2 IH2]; cbn [holds].
  - destruct o; try (exfalso; exact Ho); cbn [inst3ty].
    + rewrite !tyeqb_refl. reflexivity.
    + rewrite (tyeqb_sym (iB s1)), (tyeqb_sym (iB s2)). exact E3.
    + exact E1.
  - destruct o; try (exfalso; exact Ho); cbn [inst3ty].
    + exact E3.
    + rewrite !tyeqb_refl. reflexivity.
    + exact E2.
  - rewrite IH1, IH2. reflexivity.
Qed.

(**md
**Inside an arm of the three-arm match, a test on a variable-typed scrutinee is constant.**

Take two instantiations at which the match with the intersection arm first selects the same arm.
A test on a scrutinee whose type is `'A`, `'B` or `'T` has the same outcome at both. So in the
region an arm of that match runs in, every arm of such an inner match either always matches or
never does. One arm is enough, any further arm is unreachable, and the order of its arms cannot
matter.

The overlap check for an inner match therefore decides something only in two cases this model
has: an inner match in an arm that is written first and overlaps a later arm, as in
`region_check_accepts_what_table_check_rejects`, and an inner match on a scrutinee whose type is
not a variable.

- [s1:] one instantiation.
- [s2:] another that selects the same arm.
- [o:] the type of the inner scrutinee, one of the three variables.
- [p:] the inner test.
*)
Theorem inner_tests_decided_in_a_region
    (CA CB : cset) (s1 s2 : inst3) (o : oty3) (p : test) :
  valid CA CB s1 -> valid CA CB s2 ->
  select Equation CA CB [Both IsA IsB; IsA; IsB] s1 =
  select Equation CA CB [Both IsA IsB; IsA; IsB] s2 ->
  is_var o ->
  holds s1 (inst3ty s1 o) p = holds s2 (inst3ty s2 o) p.
Proof.
  intros V1 V2 S Ho.
  pose proof (valid_cases CA CB s1 V1) as K1. pose proof (valid_cases CA CB s2 V2) as K2.
  pose proof (ab_decided s1 K1) as A1. pose proof (ab_decided s2 K2) as A2.
  assert (E : tyeqb (iT s1) (iA s1) = tyeqb (iT s2) (iA s2) /\
              tyeqb (iT s1) (iB s1) = tyeqb (iT s2) (iB s2)).
  { unfold select in S. cbn [find matches] in S.
    destruct (tyeqb (iT s1) (iA s1)); destruct (tyeqb (iT s1) (iB s1));
      destruct (tyeqb (iT s2) (iA s2)); destruct (tyeqb (iT s2) (iB s2));
      cbn in S; try discriminate S; split; reflexivity. }
  destruct E as [E1 E2].
  apply (var_test_by_equations s1 s2 o Ho E1 E2). rewrite A1, A2, E1, E2. reflexivity.
Qed.

(**md ## Computing the region from a body

The theorems above take the region of an inner match as given. This section computes it. The
check walks the body once with a set of instantiations in hand, starting from the whole table.
At a match it narrows the set for each arm to the instantiations at which that arm is selected,
and checks the arm's body over the narrowed set. Every match is thereby checked over the
instantiations that reach it, at any depth.
*)

(** The instantiations of a set at which an arm is selected: its test succeeds and the test of
    no earlier arm does.
    - [R:] the instantiations the match runs at.
    - [u:] the type of its scrutinee at each instantiation.
    - [seen:] the tests of the earlier arms.
    - [p:] the test of the arm. *)
Definition reach (R : list inst3) (u : inst3 -> ty) (seen : list test) (p : test) : list inst3 :=
  filter (fun s => holds s (u s) p && negb (existsb (fun q => holds s (u s) q) seen)) R.

(** The type of a scrutinee at each instantiation. Where the scrutinee has no type the match is
    rejected by the type check, and the choice made here is not used.
    - [Gf:] the types of the variables in scope at each instantiation.
    - [a:] the scrutinee. *)
Definition scrut_ty (Gf : inst3 -> list ty) (a : ntm) (s : inst3) : ty :=
  match ntype s (Gf s) a with
  | Some t => t
  | None => iT s
  end.

(** The context of an arm's body at each instantiation. *)
Definition arm_ctx (Gf : inst3 -> list ty) (p : test) (s : inst3) : list ty :=
  binder_types s p ++ Gf s.

(** The context of the body of a binding at each instantiation. *)
Definition let_ctx (Gf : inst3 -> list ty) (a : ntm) (s : inst3) : list ty :=
  match ntype s (Gf s) a with
  | Some x => x :: Gf s
  | None => Gf s
  end.

(** Whether no two tests in a list are equally specific over a set of instantiations. This is
    the requirement `priority_glues` adds to the overlap check, computed. *)
Fixpoint distinct_in (R : list inst3) (u : inst3 -> ty) (l : list test) : bool :=
  match l with
  | [] => true
  | p :: r =>
      forallb (fun q => negb (le_in R u p q && le_in R u q p)) r && distinct_in R u r
  end.

(** A check of each arm of a match, given the tests of the arms before it.
    - [chk:] the check of one arm, given the tests before it, its test and its body.
    - [seen:] the tests of the arms before the ones being checked.
    - [l:] the arms still to check. *)
Fixpoint arms_ok (chk : list test -> test -> ntm -> bool) (seen : list test)
  (l : list (test * ntm)) : bool :=
  match l with
  | [] => true
  | (p, b) :: r => chk seen p b && arms_ok chk (seen ++ [p]) r
  end.

(** The overlap check of a whole body. Every match in the body passes the overlap check over the
    instantiations that reach it, and has no two arms equally specific there.
    - [R:] the instantiations that reach the body.
    - [Gf:] the types of the variables in scope at each instantiation.
    - [e:] the body. *)
Fixpoint nordered (R : list inst3) (Gf : inst3 -> list ty) (e : ntm) : bool :=
  match e with
  | NVar _ => true
  | NPrim _ a => nordered R Gf a
  | NPair a b => nordered R Gf a && nordered R Gf b
  | NFst a => nordered R Gf a
  | NSnd a => nordered R Gf a
  | NLet a b => nordered R Gf a && nordered R (let_ctx Gf a) b
  | NMatch a arms =>
      nordered R Gf a
      && ordered_in R (scrut_ty Gf a) [] (map fst arms)
      && distinct_in R (scrut_ty Gf a) (map fst arms)
      && arms_ok
           (fun seen p b => nordered (reach R (scrut_ty Gf a) seen p) (arm_ctx Gf p) b)
           [] arms
  end.

Lemma existsb_false_find {A : Type} (f : A -> bool) (l : list A) :
  existsb f l = false <-> find f l = None.
Proof.
  induction l as [| a l IH]; simpl; [tauto |].
  destruct (f a); simpl; [split; discriminate | exact IH].
Qed.

(** An arm is selected exactly where its test succeeds and no earlier test does, given that its
    test is not among the earlier ones. *)
Lemma reach_pred_iff (s : inst3) (t : ty) (seen rest : list test) (p : test) :
  ~ In p seen ->
  (holds s t p && negb (existsb (fun q => holds s t q) seen) = true <->
   find (fun q => holds s t q) (seen ++ p :: rest) = Some p).
Proof.
  intros NI. rewrite find_app. split.
  - intros H. apply andb_true_iff in H. destruct H as [Hp Hn]. apply negb_true_iff in Hn.
    apply existsb_false_find in Hn. rewrite Hn. simpl. rewrite Hp. reflexivity.
  - intros H. destruct (find (fun q => holds s t q) seen) as [q |] eqn:F.
    + injection H as ->. destruct (find_some _ _ F) as [I _]. contradiction.
    + apply existsb_false_find in F. rewrite F. simpl in H.
      destruct (holds s t p) eqn:Hp; [reflexivity |].
      destruct (find_some _ _ H) as [_ M]. cbn beta in M. rewrite Hp in M. discriminate.
Qed.

Lemma distinct_head (R : list inst3) (u : inst3 -> ty) (p : test) (l : list test) (q : test) :
  distinct_in R u (p :: l) = true -> In q l -> le_in R u p q && le_in R u q p = false.
Proof.
  cbn [distinct_in]. intros H Hq. apply andb_true_iff in H. destruct H as [H _].
  rewrite forallb_forall in H. specialize (H q Hq). cbn beta in H.
  apply negb_true_iff in H. exact H.
Qed.

Lemma distinct_tail (R : list inst3) (u : inst3 -> ty) (p : test) (l : list test) :
  distinct_in R u (p :: l) = true -> distinct_in R u l = true.
Proof.
  cbn [distinct_in]. intros H. apply andb_true_iff in H. exact (proj2 H).
Qed.

(** Among tests that are pairwise not equally specific, two that are equally specific are the
    same test. *)
Lemma distinct_antisym (R : list inst3) (u : inst3 -> ty) (l : list test) :
  distinct_in R u l = true ->
  forall p q, In p l -> In q l ->
    le_in R u p q = true -> le_in R u q p = true -> p = q.
Proof.
  induction l as [| x r IH]; intros D p q Hp Hq L1 L2; [destruct Hp |].
  destruct Hp as [<- | Hp]; destruct Hq as [<- | Hq].
  - reflexivity.
  - pose proof (distinct_head R u x r q D Hq) as E. rewrite L1, L2 in E. discriminate.
  - pose proof (distinct_head R u x r p D Hp) as E. rewrite L1, L2 in E. discriminate.
  - apply (IH (distinct_tail R u x r D) p q Hp Hq L1 L2).
Qed.

(** A test does not occur before itself in such a list. *)
Lemma distinct_notin (R : list inst3) (u : inst3 -> ty) (l1 : list test) (p : test)
  (l2 : list test) :
  distinct_in R u (l1 ++ p :: l2) = true -> ~ In p l1.
Proof.
  induction l1 as [| x r IH]; intros D I; [exact I |].
  destruct I as [-> | I].
  - pose proof (distinct_head R u p (r ++ p :: l2) p D (in_elt p r l2)) as E.
    rewrite le_in_refl in E. simpl in E. discriminate.
  - apply (IH (distinct_tail R u x _ D) I).
Qed.

(** Arms whose tests are pairwise not equally specific are told apart by their tests. *)
Lemma distinct_fst_inj (R : list inst3) (u : inst3 -> ty) (l : list (test * ntm)) :
  distinct_in R u (map fst l) = true ->
  forall y z, In y l -> In z l -> fst y = fst z -> y = z.
Proof.
  induction l as [| x r IH]; intros D y z Hy Hz E; [destruct Hy |].
  cbn [map] in D. destruct Hy as [<- | Hy]; destruct Hz as [<- | Hz].
  - reflexivity.
  - pose proof (distinct_head R u (fst x) (map fst r) (fst z) D (in_map fst r z Hz)) as K.
    rewrite <- E, le_in_refl in K. simpl in K. discriminate.
  - pose proof (distinct_head R u (fst x) (map fst r) (fst y) D (in_map fst r y Hy)) as K.
    rewrite E, le_in_refl in K. simpl in K. discriminate.
  - apply (IH (distinct_tail R u (fst x) _ D) y z Hy Hz E).
Qed.

Lemma arms_ok_split (chk : list test -> test -> ntm -> bool) :
  forall (pre : list (test * ntm)) (seen : list test) (p : test) (b : ntm)
         (post : list (test * ntm)),
    arms_ok chk seen (pre ++ (p, b) :: post) = true ->
    chk (seen ++ map fst pre) p b = true.
Proof.
  induction pre as [| [p0 b0] pre IH]; intros seen p b post H; simpl in H;
    apply andb_true_iff in H; destruct H as [H1 H2].
  - simpl. rewrite app_nil_r. exact H1.
  - specialize (IH (seen ++ [p0]) p b post H2). rewrite <- app_assoc in IH. exact IH.
Qed.

(** What the check of a match consists of. *)
Lemma nordered_match (R : list inst3) (Gf : inst3 -> list ty) (a : ntm)
  (arms : list (test * ntm)) :
  nordered R Gf (NMatch a arms) = true ->
  nordered R Gf a = true /\
  ordered_in R (scrut_ty Gf a) [] (map fst arms) = true /\
  distinct_in R (scrut_ty Gf a) (map fst arms) = true /\
  forall pre p b post, arms = pre ++ (p, b) :: post ->
    nordered (reach R (scrut_ty Gf a) (map fst pre) p) (arm_ctx Gf p) b = true.
Proof.
  cbn [nordered]. intros H.
  apply andb_true_iff in H. destruct H as [H H4].
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  intros pre p b post E. rewrite E in H4.
  exact (arms_ok_split _ pre [] p b post H4).
Qed.

(**md
**The set computed for an arm is exactly where that arm is selected.**

For an arm whose test is not among the earlier tests, an instantiation is in the computed set if
and only if it is in the set the match runs at and the match selects that arm there. So the set
handed down to an arm's body holds every instantiation at which the body runs, and no other.

- [R:] the instantiations the match runs at.
- [u:] the type of its scrutinee at each of them.
- [pre:] the arms before this one.
- [p:] the test of this arm.
- [b:] its body.
- [post:] the arms after it.
*)
Theorem reach_is_where_the_arm_is_selected
    (R : list inst3) (u : inst3 -> ty) (pre : list (test * ntm)) (p : test) (b : ntm)
    (post : list (test * ntm)) (s : inst3) :
  ~ In p (map fst pre) ->
  (In s (reach R u (map fst pre) p) <->
   In s R /\ pickn s (u s) (pre ++ (p, b) :: post) = Some (p, b)).
Proof.
  intros NI. unfold reach, pickn. rewrite filter_In, find_app. cbn beta. split.
  - intros [Hs H]. split; [exact Hs |].
    apply andb_true_iff in H. destruct H as [Hp Hn]. apply negb_true_iff in Hn.
    destruct (find (fun a => holds s (u s) (fst a)) pre) as [x |] eqn:F.
    + destruct (find_some _ _ F) as [I M]. cbn beta in M.
      assert (X : existsb (fun q => holds s (u s) q) (map fst pre) = true).
      { apply existsb_exists. exists (fst x). split; [apply in_map; exact I | exact M]. }
      rewrite X in Hn. discriminate.
    + simpl. rewrite Hp. reflexivity.
  - intros [Hs H]. split; [exact Hs |].
    destruct (find (fun a => holds s (u s) (fst a)) pre) as [x |] eqn:F.
    + injection H as ->. destruct (find_some _ _ F) as [I _]. exfalso. apply NI.
      apply (in_map fst _ _ I).
    + simpl in H. destruct (holds s (u s) p) eqn:Hp.
      * simpl. apply negb_true_iff.
        destruct (existsb (fun q => holds s (u s) q) (map fst pre)) eqn:X; [| reflexivity].
        apply existsb_exists in X. destruct X as [q [Iq Mq]].
        apply in_map_iff in Iq. destruct Iq as [y [<- Iy]].
        pose proof (find_none _ _ F y Iy) as Z. cbn beta in Z. rewrite Mq in Z. discriminate.
      * destruct (find_some _ _ H) as [_ M]. cbn beta in M. simpl in M.
        rewrite Hp in M. discriminate.
Qed.

(**md ### Reordering the arms of any match *)

(** A body with the arms of every match rearranged.
    - [f:] the rearrangement applied to each list of arms.
    - [e:] the body. *)
Fixpoint reorder (f : list (test * ntm) -> list (test * ntm)) (e : ntm) : ntm :=
  match e with
  | NVar n => NVar n
  | NPrim o a => NPrim o (reorder f a)
  | NPair a b => NPair (reorder f a) (reorder f b)
  | NFst a => NFst (reorder f a)
  | NSnd a => NSnd (reorder f a)
  | NLet a b => NLet (reorder f a) (reorder f b)
  | NMatch a arms =>
      NMatch (reorder f a) (f (map (fun pb => (fst pb, reorder f (snd pb))) arms))
  end.

Lemma forallb_eq_in {A : Type} (f g : A -> bool) (l : list A) :
  (forall a, In a l -> f a = g a) -> forallb f l = forallb g l.
Proof.
  induction l as [| a l IH]; intros H; simpl; [reflexivity |].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity |].
  intros x Hx. apply H. right. exact Hx.
Qed.

Lemma le_in_ext (R : list inst3) (u u' : inst3 -> ty) (p q : test) :
  (forall s, In s R -> u s = u' s) -> le_in R u p q = le_in R u' p q.
Proof.
  intros H. unfold le_in. apply forallb_eq_in. intros s Hs. rewrite (H s Hs). reflexivity.
Qed.

(** The overlap check over a set depends on the scrutinee's type only at that set. *)
Lemma ordered_in_ext (R : list inst3) (u u' : inst3 -> ty) (arms : list test) :
  (forall s, In s R -> u s = u' s) ->
  forall seen, ordered_in R u seen arms = ordered_in R u' seen arms.
Proof.
  intros H. induction arms as [| q rest IH]; intros seen; cbn [ordered_in]; [reflexivity |].
  rewrite IH. f_equal. apply forallb_eq_in. intros s Hs. rewrite (H s Hs).
  destruct (find (fun p => holds s (u' s) p) seen) as [p |]; [| reflexivity].
  rewrite (le_in_ext R u u' p q H). reflexivity.
Qed.

(** Under the check over a set, two lists holding the same tests, pairwise not equally specific,
    select the same test at every instantiation in the set. *)
Lemma test_selection_order_free (R : list inst3) (u : inst3 -> ty) (t1 t2 : list test) :
  ordered_in R u [] t1 = true ->
  ordered_in R u [] t2 = true ->
  (forall p, In p t1 <-> In p t2) ->
  (forall p q, In p t1 -> In q t1 ->
     le_in R u p q = true -> le_in R u q p = true -> p = q) ->
  forall s, In s R ->
    find (fun t => holds s (u s) t) t1 = find (fun t => holds s (u s) t) t2.
Proof.
  intros O1 O2 P D s Hs.
  destruct (find (fun t => holds s (u s) t) t1) as [p1 |] eqn:F1;
    destruct (find (fun t => holds s (u s) t) t2) as [p2 |] eqn:F2.
  - destruct (find_some _ _ F1) as [I1 M1]. destruct (find_some _ _ F2) as [I2 M2].
    f_equal. apply (D p1 p2 I1 (proj2 (P p2) I2)).
    + apply (inner_first_match_is_most_specific R u t1 s p1 p2 O1 Hs F1);
        [apply P; exact I2 | exact M2].
    + apply (inner_first_match_is_most_specific R u t2 s p2 p1 O2 Hs F2);
        [apply P; exact I1 | exact M1].
  - destruct (find_some _ _ F1) as [I1 M1].
    pose proof (find_none _ _ F2 p1 (proj1 (P p1) I1)) as E. cbn beta in E.
    cbn beta in M1. rewrite M1 in E. discriminate.
  - destruct (find_some _ _ F2) as [I2 M2].
    pose proof (find_none _ _ F1 p2 (proj2 (P p2) I2)) as E. cbn beta in E.
    cbn beta in M2. rewrite M2 in E. discriminate.
  - reflexivity.
Qed.

(** The rearranged arms test what the arms test. *)
Lemma reorder_tests (f : list (test * ntm) -> list (test * ntm)) (g : ntm -> ntm)
  (arms : list (test * ntm)) :
  (forall l a, In a (f l) <-> In a l) ->
  forall p, In p (map fst arms) <->
            In p (map fst (f (map (fun pb => (fst pb, g (snd pb))) arms))).
Proof.
  intros Hf p. rewrite !in_map_iff. split.
  - intros [y [E I]]. exists (fst y, g (snd y)). split; [exact E |].
    apply (proj2 (Hf _ _)). apply in_map_iff. exists y. split; [reflexivity | exact I].
  - intros [x [E I]]. apply (proj1 (Hf _ _)) in I. apply in_map_iff in I. destruct I as [y [E2 I]].
    exists y. split; [| exact I]. rewrite <- E, <- E2. reflexivity.
Qed.

(** A body that passes the check, and still passes it after its arms are rearranged, has the
    same type and value at every instantiation that reaches it. The two contexts may differ
    outside the set. *)
Lemma reorder_same (f : list (test * ntm) -> list (test * ntm)) :
  (forall l a, In a (f l) <-> In a l) ->
  forall (e : ntm) (R : list inst3) (Gf Gf' : inst3 -> list ty),
    (forall s, In s R -> Gf' s = Gf s) ->
    nordered R Gf e = true -> nordered R Gf' (reorder f e) = true ->
    forall s, In s R ->
      ntype s (Gf' s) (reorder f e) = ntype s (Gf s) e /\
      forall env : list val,
        nseval s (Gf' s) env (reorder f e) = nseval s (Gf s) env e.
Proof.
  intros Hf e.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | a arms IHa IH]
    using ntm_arms_ind; intros R Gf Gf' HG N1 N2 s Hs.
  - cbn [reorder ntype nseval]. rewrite (HG s Hs). split; reflexivity.
  - cbn [reorder nordered] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env. rewrite V. reflexivity.
  - cbn [reorder nordered] in N1, N2.
    apply andb_true_iff in N1. destruct N1 as [N1a N1b].
    apply andb_true_iff in N2. destruct N2 as [N2a N2b].
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    destruct (IHb R Gf Gf' HG N1b N2b s Hs) as [Tb Vb].
    cbn [reorder ntype nseval]. split; [rewrite Ta, Tb; reflexivity |].
    intros env. rewrite Va, Vb. reflexivity.
  - cbn [reorder nordered] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env. rewrite V. reflexivity.
  - cbn [reorder nordered] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env. rewrite V. reflexivity.
  - cbn [reorder nordered] in N1, N2.
    apply andb_true_iff in N1. destruct N1 as [N1a N1b].
    apply andb_true_iff in N2. destruct N2 as [N2a N2b].
    assert (HG' : forall s', In s' R -> let_ctx Gf' (reorder f a) s' = let_ctx Gf a s').
    { intros s' Hs'. unfold let_ctx. destruct (IHa R Gf Gf' HG N1a N2a s' Hs') as [T _].
      rewrite T, (HG s' Hs'). reflexivity. }
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    destruct (IHb R (let_ctx Gf a) (let_ctx Gf' (reorder f a)) HG' N1b N2b s Hs) as [Tb Vb].
    unfold let_ctx in Tb, Vb. rewrite Ta in Tb, Vb.
    cbn [reorder ntype nseval]. rewrite Ta.
    destruct (ntype s (Gf s) a) as [x |]; [| split; reflexivity].
    split; [exact Tb |]. intros env. rewrite Va.
    destruct (nseval s (Gf s) env a) as [v |]; [apply Vb | reflexivity].
  - cbn [reorder] in N2. cbn [reorder].
    apply nordered_match in N1. destruct N1 as [N1a [O1 [D1 A1]]].
    apply nordered_match in N2. destruct N2 as [N2a [O2 [D2 A2]]].
    remember (f (map (fun pb => (fst pb, reorder f (snd pb))) arms)) as arms' eqn:EA.
    assert (U : forall s', In s' R ->
              scrut_ty Gf' (reorder f a) s' = scrut_ty Gf a s').
    { intros s' Hs'. unfold scrut_ty. destruct (IHa R Gf Gf' HG N1a N2a s' Hs') as [T _].
      rewrite T. reflexivity. }
    rewrite (ordered_in_ext R _ _ (map fst arms') U) in O2.
    assert (TM : forall p, In p (map fst arms) <-> In p (map fst arms')).
    { rewrite EA. apply reorder_tests. exact Hf. }
    pose proof (test_selection_order_free R (scrut_ty Gf a) (map fst arms) (map fst arms')
                  O1 O2 TM (distinct_antisym R _ _ D1)) as SEL.
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    assert (K : forall t, ntype s (Gf s) a = Some t ->
              match pickn s t arms with
              | None => pickn s t arms' = None
              | Some (p, b) =>
                  pickn s t arms' = Some (p, reorder f b) /\
                  ntype s (binder_types s p ++ Gf' s) (reorder f b) =
                  ntype s (binder_types s p ++ Gf s) b /\
                  forall env : list val,
                    nseval s (binder_types s p ++ Gf' s) env (reorder f b) =
                    nseval s (binder_types s p ++ Gf s) env b
              end).
    { intros t Ht.
      assert (Us : scrut_ty Gf a s = t) by (unfold scrut_ty; rewrite Ht; reflexivity).
      pose proof (SEL s Hs) as S. rewrite Us in S. rewrite !find_map in S. unfold pickn.
      destruct (find (fun a0 => holds s t (fst a0)) arms) as [[p b] |] eqn:F1.
      - destruct (find (fun a0 => holds s t (fst a0)) arms') as [[p' b'] |] eqn:F2;
          [| discriminate S].
        simpl in S. injection S as <-.
        destruct (find_some _ _ F1) as [I1 _]. destruct (find_some _ _ F2) as [I2 _].
        pose proof I2 as I2'. rewrite EA in I2'. apply (proj1 (Hf _ _)) in I2'.
        apply in_map_iff in I2'. destruct I2' as [[py pb] [E Iy]]. simpl in E.
        injection E as E1 E2. subst py b'.
        pose proof (distinct_fst_inj R _ arms D1 (p, pb) (p, b) Iy I1 eq_refl) as Q.
        injection Q as ->.
        split; [reflexivity |].
        destruct (in_split _ _ I1) as [pre [post Ea]].
        destruct (in_split _ _ I2) as [pre' [post' Ea']].
        pose proof (A1 pre p b post Ea) as B1.
        pose proof (A2 pre' p (reorder f b) post' Ea') as B2.
        assert (NI1 : ~ In p (map fst pre)).
        { pose proof D1 as D. rewrite Ea, map_app in D. exact (distinct_notin _ _ _ _ _ D). }
        assert (NI2 : ~ In p (map fst pre')).
        { pose proof D2 as D. rewrite Ea', map_app in D. exact (distinct_notin _ _ _ _ _ D). }
        assert (RE : reach R (scrut_ty Gf' (reorder f a)) (map fst pre') p =
                     reach R (scrut_ty Gf a) (map fst pre) p).
        { unfold reach. apply filter_ext_in. intros s' Hs'. rewrite (U s' Hs').
          apply Bool.eq_iff_eq_true.
          rewrite (reach_pred_iff s' _ (map fst pre') (map fst post') p NI2).
          rewrite (reach_pred_iff s' _ (map fst pre) (map fst post) p NI1).
          pose proof (SEL s' Hs') as S'. rewrite Ea, Ea', !map_app in S'.
          cbn [map fst] in S'. rewrite S'. tauto. }
        rewrite RE in B2.
        assert (HGa : forall s', In s' (reach R (scrut_ty Gf a) (map fst pre) p) ->
                  arm_ctx Gf' p s' = arm_ctx Gf p s').
        { intros s' Hs'. unfold reach in Hs'. apply filter_In in Hs'.
          unfold arm_ctx. rewrite (HG s' (proj1 Hs')). reflexivity. }
        assert (Sin : In s (reach R (scrut_ty Gf a) (map fst pre) p)).
        { unfold reach. apply filter_In. split; [exact Hs |]. cbn beta. rewrite Us.
          apply (reach_pred_iff s t (map fst pre) (map fst post) p NI1).
          pose proof (find_map (fun q => holds s t q) fst arms) as FM. cbn beta in FM.
          rewrite F1, Ea, map_app in FM. exact FM. }
        rewrite Forall_forall in IH.
        destruct (IH (p, b) I1 _ (arm_ctx Gf p) (arm_ctx Gf' p) HGa B1 B2 s Sin) as [T V].
        unfold arm_ctx in T, V. split; assumption.
      - destruct (find (fun a0 => holds s t (fst a0)) arms') as [x |] eqn:F2;
          [simpl in S; discriminate S | reflexivity]. }
    split.
    + rewrite !ntype_match, Ta. destruct (ntype s (Gf s) a) as [t |]; [| reflexivity].
      specialize (K t eq_refl). destruct (pickn s t arms) as [[p b] |].
      * destruct K as [K1 [K2 _]]. rewrite K1. exact K2.
      * rewrite K. reflexivity.
    + intros env. rewrite !nseval_match, Ta, Va.
      destruct (ntype s (Gf s) a) as [t |]; [| reflexivity].
      destruct (nseval s (Gf s) env a) as [v |]; [| reflexivity].
      specialize (K t eq_refl). destruct (pickn s t arms) as [[p b] |].
      * destruct K as [K1 [_ K3]]. rewrite K1. apply K3.
      * rewrite K. reflexivity.
Qed.

(**md
**A body that passes the check means the same after any rearrangement of its arms.**

Take a body, and the same body with the arms of every match rearranged, at any depth. If both
pass the overlap check over a set of instantiations, they have the same type and return the same
value at every instantiation in the set. The check uses the region it computes for each match,
and nothing else is supplied.

This is the statement the region is computed for. `inner_order_is_irrelevant` assumes a set
that contains the instantiations one match runs at. Here the check finds that set for every
match in the body.

- [f:] the rearrangement applied to each list of arms. It keeps the same arms.
- [e:] the body.
- [R:] the instantiations that reach the body.
- [Gf:] the types of the variables in scope at each of them.
*)
Theorem reordering_arms_changes_nothing
    (f : list (test * ntm) -> list (test * ntm)) (e : ntm)
    (R : list inst3) (Gf : inst3 -> list ty) :
  (forall l a, In a (f l) <-> In a l) ->
  nordered R Gf e = true -> nordered R Gf (reorder f e) = true ->
  forall s, In s R ->
    ntype s (Gf s) (reorder f e) = ntype s (Gf s) e /\
    forall env : list val, nseval s (Gf s) env (reorder f e) = nseval s (Gf s) env e.
Proof.
  intros Hf N1 N2. exact (reorder_same f Hf e R Gf Gf (fun _ _ => eq_refl) N1 N2).
Qed.

(** The context of a definition's body at each instantiation: the scrutinee, then the other
    parameters. *)
Definition top_ctx (G : list oty3) (s : inst3) : list ty := iT s :: map (inst3ty s) G.

(**md
**A definition that passes the check may have the arms of any of its matches rearranged.**

For a definition, the check starts from the whole table. If the definition and its rearrangement
both pass, the rearrangement passes the type check exactly when the definition does, and at
every instantiation that satisfies the constraints the two return the same result.

- [G:] the types of the other parameters.
- [e:] the body.
- [res:] the declared result type.
- [f:] the rearrangement applied to each list of arms.
*)
Theorem reordered_definition_means_the_same
    (CA CB : cset) (G : list oty3) (e : ntm) (res : oty3)
    (f : list (test * ntm) -> list (test * ntm)) :
  (forall l a, In a (f l) <-> In a l) ->
  nordered (table CA CB) (top_ctx G) e = true ->
  nordered (table CA CB) (top_ctx G) (reorder f e) = true ->
  ncheck CA CB G (reorder f e) res = ncheck CA CB G e res /\
  forall (s : inst3) (env : list val) (x : val),
    valid CA CB s ->
    nseval s (iT s :: map (inst3ty s) G) (x :: env) (reorder f e) =
    nseval s (iT s :: map (inst3ty s) G) (x :: env) e.
Proof.
  intros Hf N1 N2.
  pose proof (reordering_arms_changes_nothing f e (table CA CB) (top_ctx G) Hf N1 N2) as K.
  split.
  - unfold ncheck. apply forallb_eq_in. intros s Hs. destruct (K s Hs) as [T _].
    unfold top_ctx in T. rewrite T. reflexivity.
  - intros s env x V. destruct (K s (proj2 (table_iff_valid CA CB s) V)) as [_ E].
    exact (E (x :: env)).
Qed.

(** A match with one arm on each variable, and the same match with its arms swapped. *)
Definition two_arms : ntm := NMatch (NVar 0) [(IsA, NVar 0); (IsB, NVar 0)].

(**md
**The check accepts a match in both orders when its arms cannot overlap.**

For `'A : (x)` and `'B : (y)` with `x` and `y` different types, the two-arm match passes the
check, and so does the same match with its arms reversed. So the hypotheses of the two theorems
above can be met by a match whose arms are in fact reordered.

- [x:] the only member of the first set.
- [y:] the only member of the second set.
*)
Theorem check_accepts_both_orders (x y : ty) :
  x <> y ->
  nordered (table [x] [y]) (top_ctx []) two_arms = true /\
  nordered (table [x] [y]) (top_ctx []) (reorder (@rev (test * ntm)) two_arms) = true.
Proof.
  intros N.
  assert (Q1 : tyeqb x y = false) by (apply tyeqb_false; exact N).
  assert (Q2 : tyeqb y x = false) by (apply tyeqb_false; congruence).
  assert (T : table [x] [y] = [Inst x y x; Inst x y y]).
  { unfold table. cbn [flat_map app]. unfold rows. rewrite Q1. reflexivity. }
  rewrite T. unfold two_arms.
  split;
    cbn [reorder map rev app fst snd nordered arms_ok ordered_in distinct_in forallb find
         existsb reach filter le_in holds scrut_ty ntype nth_error top_ctx iT iA iB];
    rewrite ?tyeqb_refl, ?Q1, ?Q2;
    cbn [reorder map rev app fst snd nordered arms_ok ordered_in distinct_in forallb find
         existsb reach filter le_in holds scrut_ty ntype nth_error top_ctx iT iA iB
         andb orb negb implb];
    rewrite ?tyeqb_refl, ?Q1, ?Q2; reflexivity.
Qed.

(**md ## Agreement in an inner match

[Bodies](Clef.RFC0002.Bodies.html) gives two ways to make arm order irrelevant: priority, where
the more specific of two overlapping arms wins, and agreement, where the two bodies compute the
same result on the overlap. The sections above carry priority to an inner match. This section
carries agreement.

Two things change from Bodies. The overlap is taken over the region of the match, as the overlap
check is. And agreement includes the type of the two bodies, because the check of this module
types only the arm selected: if the other arm were selected in another order, its body must have
the same type there.
*)

(** One test is strictly more specific than another over a set of instantiations.
    - [R:] the instantiations considered.
    - [u:] the type of the scrutinee at each instantiation.
    - [p:] the more specific test.
    - [q:] the more general test. *)
Definition lt_in (R : list inst3) (u : inst3 -> ty) (p q : test) : bool :=
  le_in R u p q && negb (le_in R u q p).

(** Two arms agree at an instantiation when their bodies have the same type there and return the
    same result for every scrutinee of the scrutinee's type.
    - [s:] the instantiation.
    - [G:] the types of the variables in scope around the match.
    - [t:] the type of the scrutinee.
    - [a:] one arm.
    - [b:] the other arm. *)
Definition agree_in (s : inst3) (G : list ty) (t : ty) (a b : test * ntm) : Prop :=
  ntype s (binder_types s (fst a) ++ G) (snd a) =
  ntype s (binder_types s (fst b) ++ G) (snd b) /\
  forall (env : list val) (v : val), has_ty v t ->
    nseval s (binder_types s (fst a) ++ G) (repeat v (arity (fst a)) ++ env) (snd a) =
    nseval s (binder_types s (fst b) ++ G) (repeat v (arity (fst b)) ++ env) (snd b).

(** The arms of a match glue over a set of instantiations when, at each of them, the selected
    arm is strictly more specific over the set than each other arm that matches, or agrees with
    it.
    - [R:] the instantiations the match is checked over.
    - [u:] the type of the scrutinee at each of them.
    - [Gf:] the types of the variables in scope at each of them.
    - [arms:] the arms. *)
Definition glues_in (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty)
  (arms : list (test * ntm)) : Prop :=
  forall (s : inst3) (p q : test * ntm),
    In s R ->
    pickn s (u s) arms = Some p ->
    In q arms -> holds s (u s) (fst q) = true ->
    lt_in R u (fst p) (fst q) = true \/ agree_in s (Gf s) (u s) p q.

Lemma agree_in_refl (s : inst3) (G : list ty) (t : ty) (a : test * ntm) : agree_in s G t a a.
Proof.
  split; [reflexivity | intros; reflexivity].
Qed.

Lemma agree_in_sym (s : inst3) (G : list ty) (t : ty) (a b : test * ntm) :
  agree_in s G t a b -> agree_in s G t b a.
Proof.
  intros [T V]. split; [symmetry; exact T |]. intros env v Hv. symmetry. exact (V env v Hv).
Qed.

Lemma lt_in_asym (R : list inst3) (u : inst3 -> ty) (p q : test) :
  lt_in R u p q = true -> lt_in R u q p = true -> False.
Proof.
  unfold lt_in. intros H1 H2. apply andb_true_iff in H1. apply andb_true_iff in H2.
  destruct H1 as [H1 _]. destruct H2 as [_ H2]. rewrite H1 in H2. discriminate.
Qed.

Lemma lt_in_ext (R : list inst3) (u u' : inst3 -> ty) (p q : test) :
  (forall s, In s R -> u s = u' s) -> lt_in R u p q = lt_in R u' p q.
Proof.
  intros H. unfold lt_in. rewrite (le_in_ext R u u' p q H), (le_in_ext R u u' q p H).
  reflexivity.
Qed.

(** A body that has a type returns a value of that type, on values of the types in scope. This
    is the safety theorem of RFC 0001 carried through the specialization, and it rests on the
    same assumption about witnesses. *)
Lemma nseval_typed (s : inst3) (G : list ty) (e : ntm) (t : ty) (env : list val) :
  ntype s G e = Some t -> Forall2 has_ty env G ->
  exists v, nseval s G env e = Some v /\ has_ty v t.
Proof.
  intros T HE. destruct (typed_body_specializes s e G t T) as [m [Hm Ht]].
  rewrite (nested_specialization_preserves_meaning s e G m Hm).
  exact (specialization_is_safe m G env t HE Ht).
Qed.

(** The binders of an arm that matches hold values of their types. *)
Lemma binders_typed (s : inst3) (t : ty) (p : test) (v : val) (env : list val) (G : list ty) :
  holds s t p = true -> has_ty v t -> Forall2 has_ty env G ->
  Forall2 has_ty (repeat v (arity p) ++ env) (binder_types s p ++ G).
Proof.
  intros M Hv HE. rewrite (holds_binders s t p M).
  induction (arity p) as [| k IH]; simpl; [exact HE | constructor; assumption].
Qed.

(** Under gluing, two lists holding the same arms select arms that agree. *)
Lemma glued_selection
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (l1 l2 : list (test * ntm))
    (s : inst3) :
  glues_in R u Gf l1 -> glues_in R u Gf l2 ->
  (forall a, In a l1 <-> In a l2) ->
  In s R ->
  match pickn s (u s) l1 with
  | Some a =>
      match pickn s (u s) l2 with
      | Some b => agree_in s (Gf s) (u s) a b
      | None => False
      end
  | None => pickn s (u s) l2 = None
  end.
Proof.
  intros G1 G2 P Hs.
  destruct (pickn s (u s) l1) as [a1 |] eqn:F1; destruct (pickn s (u s) l2) as [a2 |] eqn:F2.
  - destruct (find_some _ _ F1) as [I1 M1]. destruct (find_some _ _ F2) as [I2 M2].
    cbn beta in M1, M2.
    destruct (G1 s a1 a2 Hs F1 (proj2 (P a2) I2) M2) as [L1 | A1]; [| exact A1].
    destruct (G2 s a2 a1 Hs F2 (proj1 (P a1) I1) M1) as [L2 | A2].
    + destruct (lt_in_asym R u _ _ L1 L2).
    + apply agree_in_sym. exact A2.
  - destruct (find_some _ _ F1) as [I1 M1]. cbn beta in M1.
    pose proof (find_none _ _ F2 a1 (proj1 (P a1) I1)) as E. cbn beta in E.
    rewrite M1 in E. discriminate.
  - destruct (find_some _ _ F2) as [I2 M2]. cbn beta in M2.
    pose proof (find_none _ _ F1 a2 (proj2 (P a2) I2)) as E. cbn beta in E.
    rewrite M2 in E. discriminate.
  - reflexivity.
Qed.

(**md
**Inner arms that glue compute the same result in any order.**

Take two lists holding the same arms, both gluing over a set of instantiations. At every
instantiation in the set where the scrutinee has the stated type, the two matches have the same
type, and on values of the types in scope they return the same value. The arm selected may differ
between the two orders. Where it does, the two arms agree.

This is `glued_order_irrelevant` for an inner match. It covers priority, agreement, and a match
that uses each on different overlaps. It uses the assumption that every witness is implemented
at its declared type, because agreement is asked only for scrutinees of the scrutinee's type, and
that the scrutinee evaluates to such a value is the safety theorem.

- [R:] the instantiations the match is checked over.
- [u:] the type of the scrutinee at each of them.
- [Gf:] the types of the variables in scope at each of them.
- [l1:] the arms in one order.
- [l2:] the same arms in another order.
- [e:] the scrutinee.
*)
Theorem inner_glued_order_irrelevant
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (l1 l2 : list (test * ntm))
    (s : inst3) (e : ntm) :
  glues_in R u Gf l1 -> glues_in R u Gf l2 ->
  (forall a, In a l1 <-> In a l2) ->
  In s R -> ntype s (Gf s) e = Some (u s) ->
  ntype s (Gf s) (NMatch e l1) = ntype s (Gf s) (NMatch e l2) /\
  forall env : list val, Forall2 has_ty env (Gf s) ->
    nseval s (Gf s) env (NMatch e l1) = nseval s (Gf s) env (NMatch e l2).
Proof.
  intros G1 G2 P Hs H.
  pose proof (glued_selection R u Gf l1 l2 s G1 G2 P Hs) as K. split.
  - rewrite !ntype_match, H.
    destruct (pickn s (u s) l1) as [[p1 b1] |].
    + destruct (pickn s (u s) l2) as [[p2 b2] |]; [exact (proj1 K) | destruct K].
    + rewrite K. reflexivity.
  - intros env HE. rewrite !nseval_match, H.
    destruct (nseval_typed s (Gf s) e (u s) env H HE) as [v [Ev Hv]]. rewrite Ev.
    destruct (pickn s (u s) l1) as [[p1 b1] |].
    + destruct (pickn s (u s) l2) as [[p2 b2] |]; [exact (proj2 K env v Hv) | destruct K].
    + rewrite K. reflexivity.
Qed.

(**md
**The overlap check over a region glues when no two arms are equally specific there.**

If the arms of a match pass the overlap check over a set of instantiations, and no two different
arms are equally specific over the set, the arms glue over it. So priority is one way to meet the
gluing condition for an inner match, and `inner_order_is_irrelevant` is a case of the theorem
above. This is `priority_glues` for an inner match.

- [R:] the instantiations the match is checked over.
- [u:] the type of the scrutinee at each of them.
- [Gf:] the types of the variables in scope at each of them.
- [arms:] the arms.
*)
Theorem inner_priority_glues
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (arms : list (test * ntm)) :
  ordered_in R u [] (map fst arms) = true ->
  (forall a b, In a arms -> In b arms ->
     le_in R u (fst a) (fst b) = true -> le_in R u (fst b) (fst a) = true -> a = b) ->
  glues_in R u Gf arms.
Proof.
  intros O D s p q Hs F Hq M. destruct (find_some _ _ F) as [Hp _].
  assert (L : le_in R u (fst p) (fst q) = true).
  { apply (inner_first_match_is_most_specific R u (map fst arms) s (fst p) (fst q) O Hs).
    - rewrite find_map. unfold pickn in F. rewrite F. reflexivity.
    - apply in_map. exact Hq.
    - exact M. }
  destruct (le_in R u (fst q) (fst p)) eqn:L2.
  - right. rewrite (D p q Hp Hq L L2). apply agree_in_refl.
  - left. unfold lt_in. rewrite L, L2. reflexivity.
Qed.

(** Two arms with the same body and the same number of binders agree wherever both tests
    succeed. There the binders of both are at the scrutinee's type. *)
Lemma same_body_agrees (s : inst3) (G : list ty) (t : ty) (p q : test) (b : ntm) :
  holds s t p = true -> holds s t q = true -> arity p = arity q ->
  agree_in s G t (p, b) (q, b).
Proof.
  intros Hp Hq E. unfold agree_in. cbn [fst snd].
  rewrite (holds_binders s t p Hp), (holds_binders s t q Hq), E.
  split; [reflexivity | intros; reflexivity].
Qed.

(**md
**Two inner arms with the same body glue, whatever the region is.**

Two arms that bind the same number of names and have the same body glue over every set of
instantiations, on every scrutinee. Where both tests succeed, the binders of each arm are at the
scrutinee's type, so the one body is typed and run the same way under either test. The body may
hold further matches. This is the structural form of agreement, and `same_body_glues` is the case
of the two tests `:? 'A` and `:? 'B` on the parameter of type `'T`.

- [p:] the test of one arm.
- [q:] the test of the other.
- [b:] the body both arms have.
*)
Theorem inner_same_body_glues
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (p q : test) (b : ntm) :
  arity p = arity q -> glues_in R u Gf [(p, b); (q, b)].
Proof.
  intros E s a c Hs F Hc M. right. destruct (find_some _ _ F) as [Ha Ma]. cbn beta in Ma.
  simpl in Ha, Hc.
  destruct Ha as [<- | [<- | []]]; destruct Hc as [<- | [<- | []]]; cbn [fst] in Ma, M;
    apply same_body_agrees;
    first [assumption | reflexivity | exact E | symmetry; exact E].
Qed.

(**md
**Agreement accepts an inner match the overlap check over its region rejects.**

Take `'A : (x | y)` and `'B : (y)`, and an inner match on a scrutinee of type `'T` inside an arm
`:? 'A` that is written first. Its arms are `:? 'A` then `:? 'B`, with the same body. In that
region `:? 'A` always succeeds and `:? 'B` succeeds only where the two variables are the same
type, so the general arm is written before the specific one and the overlap check over the region
rejects the match. The arms glue all the same, because the body that runs is the same either way.

`region_check_accepts_what_table_check_rejects` has the same two arms in the other order, which
priority accepts. Agreement accepts both orders.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
- [b:] the body both arms have.
- [Gf:] the types of the variables in scope at each instantiation.
*)
Theorem inner_agreement_accepts_what_region_check_rejects
    (x y : ty) (b : ntm) (Gf : inst3 -> list ty) :
  x <> y ->
  glues_in (restrict (table [x; y] [y]) iT IsA) iT Gf [(IsA, b); (IsB, b)] /\
  ordered_in (restrict (table [x; y] [y]) iT IsA) iT [] [IsA; IsB] = false.
Proof.
  intros N. split; [apply inner_same_body_glues; reflexivity |].
  destruct (ordered_in (restrict (table [x; y] [y]) iT IsA) iT [] [IsA; IsB]) eqn:O;
    [| reflexivity].
  exfalso.
  assert (I1 : In (Inst y y y) (restrict (table [x; y] [y]) iT IsA)).
  { unfold restrict. apply filter_In. split.
    - apply table_iff_valid. unfold valid, sat. simpl. intuition.
    - cbn [holds iT iA]. apply tyeqb_refl. }
  assert (I2 : In (Inst x y x) (restrict (table [x; y] [y]) iT IsA)).
  { unfold restrict. apply filter_In. split.
    - apply table_iff_valid. unfold valid, sat. simpl. intuition.
    - cbn [holds iT iA]. apply tyeqb_refl. }
  assert (L : le_in (restrict (table [x; y] [y]) iT IsA) iT IsA IsB = true).
  { apply (inner_first_match_is_most_specific _ iT [IsA; IsB] (Inst y y y) IsA IsB O I1).
    - cbn [find holds iT iA]. rewrite tyeqb_refl. reflexivity.
    - simpl. auto.
    - cbn [holds iT iB]. apply tyeqb_refl. }
  apply N. apply tyeqb_iff.
  exact (proj1 (le_in_iff _ iT IsA IsB) L (Inst x y x) I2 (tyeqb_refl x)).
Qed.

(**md ### Gluing a whole body

The overlap check of a whole body hands an arm's body the instantiations at which the arm is
selected. Under agreement that set is too small. When two arms agree, either may be written
first, so an arm's body can run at any instantiation where its test succeeds. The gluing
condition for a whole body therefore checks an arm's body over every instantiation in the region
where the arm's test succeeds. `selected_set_gluing_falsified` below shows that the smaller set
is unsound for this condition.
*)

(** The gluing condition of a whole body. The arms of every match in the body glue over the
    instantiations that can reach it, and the body of each arm is examined wherever the arm's
    test succeeds.
    - [R:] the instantiations that can reach the body.
    - [Gf:] the types of the variables in scope at each instantiation.
    - [e:] the body. *)
Fixpoint nglued (R : list inst3) (Gf : inst3 -> list ty) (e : ntm) : Prop :=
  match e with
  | NVar _ => True
  | NPrim _ a => nglued R Gf a
  | NPair a b => nglued R Gf a /\ nglued R Gf b
  | NFst a => nglued R Gf a
  | NSnd a => nglued R Gf a
  | NLet a b => nglued R Gf a /\ nglued R (let_ctx Gf a) b
  | NMatch a arms =>
      nglued R Gf a /\
      glues_in R (scrut_ty Gf a) Gf arms /\
      (fix go (l : list (test * ntm)) : Prop :=
         match l with
         | [] => True
         | (p, b) :: r =>
             nglued (restrict R (scrut_ty Gf a) p) (arm_ctx Gf p) b /\ go r
         end) arms
  end.

(** What the gluing condition of a match consists of. *)
Lemma nglued_match (R : list inst3) (Gf : inst3 -> list ty) (a : ntm)
  (arms : list (test * ntm)) :
  nglued R Gf (NMatch a arms) ->
  nglued R Gf a /\
  glues_in R (scrut_ty Gf a) Gf arms /\
  forall p b, In (p, b) arms -> nglued (restrict R (scrut_ty Gf a) p) (arm_ctx Gf p) b.
Proof.
  cbn [nglued]. intros [H1 [H2 H3]]. split; [exact H1 |]. split; [exact H2 |].
  clear H1 H2. induction arms as [| [p0 b0] r IH]; intros p b I; [destruct I |].
  destruct H3 as [H3 H4]. destruct I as [E | I].
  - injection E as <- <-. exact H3.
  - exact (IH H4 p b I).
Qed.

(** A body that glues, and still glues after its arms are rearranged, has the same type and, on
    values of the types in scope, the same value at every instantiation that reaches it. The two
    contexts may differ outside the set. *)
Lemma glued_reorder_same (f : list (test * ntm) -> list (test * ntm)) :
  (forall l a, In a (f l) <-> In a l) ->
  forall (e : ntm) (R : list inst3) (Gf Gf' : inst3 -> list ty),
    (forall s, In s R -> Gf' s = Gf s) ->
    nglued R Gf e -> nglued R Gf' (reorder f e) ->
    forall s, In s R ->
      ntype s (Gf' s) (reorder f e) = ntype s (Gf s) e /\
      forall env : list val, Forall2 has_ty env (Gf s) ->
        nseval s (Gf' s) env (reorder f e) = nseval s (Gf s) env e.
Proof.
  intros Hf e.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | a arms IHa IH]
    using ntm_arms_ind; intros R Gf Gf' HG N1 N2 s Hs.
  - cbn [reorder ntype nseval]. rewrite (HG s Hs). split; [reflexivity | intros; reflexivity].
  - cbn [reorder nglued] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env HE. rewrite (V env HE). reflexivity.
  - cbn [reorder nglued] in N1, N2. destruct N1 as [N1a N1b]. destruct N2 as [N2a N2b].
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    destruct (IHb R Gf Gf' HG N1b N2b s Hs) as [Tb Vb].
    cbn [reorder ntype nseval]. split; [rewrite Ta, Tb; reflexivity |].
    intros env HE. rewrite (Va env HE), (Vb env HE). reflexivity.
  - cbn [reorder nglued] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env HE. rewrite (V env HE). reflexivity.
  - cbn [reorder nglued] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env HE. rewrite (V env HE). reflexivity.
  - cbn [reorder nglued] in N1, N2. destruct N1 as [N1a N1b]. destruct N2 as [N2a N2b].
    assert (HG' : forall s', In s' R -> let_ctx Gf' (reorder f a) s' = let_ctx Gf a s').
    { intros s' Hs'. unfold let_ctx. destruct (IHa R Gf Gf' HG N1a N2a s' Hs') as [T _].
      rewrite T, (HG s' Hs'). reflexivity. }
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    destruct (IHb R (let_ctx Gf a) (let_ctx Gf' (reorder f a)) HG' N1b N2b s Hs) as [Tb Vb].
    unfold let_ctx in Tb, Vb. rewrite Ta in Tb, Vb.
    cbn [reorder ntype nseval]. rewrite Ta.
    destruct (ntype s (Gf s) a) as [x |] eqn:Tx; [| split; [reflexivity | intros; reflexivity]].
    cbn beta iota in Tb, Vb.
    split; [exact Tb |]. intros env HE. rewrite (Va env HE).
    destruct (nseval_typed s (Gf s) a x env Tx HE) as [v [Ev Hv]]. rewrite Ev.
    apply Vb. constructor; assumption.
  - cbn [reorder] in N2. cbn [reorder].
    apply nglued_match in N1. destruct N1 as [N1a [GL1 A1]].
    apply nglued_match in N2. destruct N2 as [N2a [GL2 A2]].
    remember (f (map (fun pb => (fst pb, reorder f (snd pb))) arms)) as arms' eqn:EA.
    assert (U : forall s', In s' R ->
              scrut_ty Gf' (reorder f a) s' = scrut_ty Gf a s').
    { intros s' Hs'. unfold scrut_ty. destruct (IHa R Gf Gf' HG N1a N2a s' Hs') as [T _].
      rewrite T. reflexivity. }
    assert (INV : forall q b', In (q, b') arms' ->
              exists bq, In (q, bq) arms /\ b' = reorder f bq).
    { intros q b' I. rewrite EA in I. apply (proj1 (Hf _ _)) in I. apply in_map_iff in I.
      destruct I as [[py pb] [E Iy]]. cbn [fst snd] in E. injection E as -> <-.
      exists pb. split; [exact Iy | reflexivity]. }
    assert (FWD : forall p b, In (p, b) arms -> In (p, reorder f b) arms').
    { intros p b I. rewrite EA. apply (proj2 (Hf _ _)). apply in_map_iff.
      exists (p, b). split; [reflexivity | exact I]. }
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    rewrite Forall_forall in IH.
    assert (ARM : forall t p b, ntype s (Gf s) a = Some t -> In (p, b) arms ->
              holds s t p = true ->
              ntype s (binder_types s p ++ Gf' s) (reorder f b) =
              ntype s (binder_types s p ++ Gf s) b /\
              forall (env : list val) (v : val), Forall2 has_ty env (Gf s) -> has_ty v t ->
                nseval s (binder_types s p ++ Gf' s) (repeat v (arity p) ++ env) (reorder f b) =
                nseval s (binder_types s p ++ Gf s) (repeat v (arity p) ++ env) b).
    { intros t p b Ht I M.
      assert (Us : scrut_ty Gf a s = t) by (unfold scrut_ty; rewrite Ht; reflexivity).
      pose proof (A1 p b I) as B1. pose proof (A2 p (reorder f b) (FWD p b I)) as B2.
      assert (RE : restrict R (scrut_ty Gf' (reorder f a)) p = restrict R (scrut_ty Gf a) p).
      { unfold restrict. apply filter_ext_in. intros s' Hs'. rewrite (U s' Hs'). reflexivity. }
      rewrite RE in B2.
      assert (HGa : forall s', In s' (restrict R (scrut_ty Gf a) p) ->
                arm_ctx Gf' p s' = arm_ctx Gf p s').
      { intros s' Hs'. unfold restrict in Hs'. apply filter_In in Hs'.
        unfold arm_ctx. rewrite (HG s' (proj1 Hs')). reflexivity. }
      assert (Sin : In s (restrict R (scrut_ty Gf a) p)).
      { unfold restrict. apply filter_In. split; [exact Hs |]. cbn beta. rewrite Us. exact M. }
      destruct (IH (p, b) I _ (arm_ctx Gf p) (arm_ctx Gf' p) HGa B1 B2 s Sin) as [T V].
      unfold arm_ctx in T, V. cbn [snd] in T, V. split; [exact T |].
      intros env v HE Hv. apply V. exact (binders_typed s t p v env (Gf s) M Hv HE). }
    assert (K : forall t, ntype s (Gf s) a = Some t ->
              match pickn s t arms with
              | None => pickn s t arms' = None
              | Some (p, b) =>
                  exists q b', pickn s t arms' = Some (q, b') /\
                  ntype s (binder_types s q ++ Gf' s) b' =
                  ntype s (binder_types s p ++ Gf s) b /\
                  forall (env : list val) (v : val), Forall2 has_ty env (Gf s) -> has_ty v t ->
                    nseval s (binder_types s q ++ Gf' s) (repeat v (arity q) ++ env) b' =
                    nseval s (binder_types s p ++ Gf s) (repeat v (arity p) ++ env) b
              end).
    { intros t Ht.
      assert (Us : scrut_ty Gf a s = t) by (unfold scrut_ty; rewrite Ht; reflexivity).
      assert (Us' : scrut_ty Gf' (reorder f a) s = t) by (rewrite (U s Hs); exact Us).
      destruct (pickn s t arms) as [[p b] |] eqn:F1.
      - destruct (find_some _ _ F1) as [I1 M1]. cbn beta in M1. cbn [fst] in M1.
        destruct (pickn s t arms') as [[q b'] |] eqn:F2.
        + destruct (find_some _ _ F2) as [I2 M2]. cbn beta in M2. cbn [fst] in M2.
          destruct (INV q b' I2) as [bq [Iq ->]].
          exists q, (reorder f bq). split; [reflexivity |].
          destruct (ARM t p b Ht I1 M1) as [TP VP].
          destruct (ARM t q bq Ht Iq M2) as [TQ VQ].
          assert (F1' : pickn s (scrut_ty Gf a s) arms = Some (p, b))
            by (rewrite Us; exact F1).
          assert (M2' : holds s (scrut_ty Gf a s) (fst (q, bq)) = true)
            by (rewrite Us; exact M2).
          destruct (GL1 s (p, b) (q, bq) Hs F1' Iq M2') as [L1 | [AT AV]].
          * assert (F2' : pickn s (scrut_ty Gf' (reorder f a) s) arms' =
                          Some (q, reorder f bq)) by (rewrite Us'; exact F2).
            assert (M1' : holds s (scrut_ty Gf' (reorder f a) s) (fst (p, reorder f b)) = true)
              by (rewrite Us'; exact M1).
            destruct (GL2 s (q, reorder f bq) (p, reorder f b) Hs F2' (FWD p b I1) M1')
              as [L2 | [BT BV]].
            -- exfalso. rewrite (lt_in_ext R _ _ _ _ U) in L2. cbn [fst] in L1, L2.
               exact (lt_in_asym R _ _ _ L1 L2).
            -- cbn [fst snd] in BT, BV. rewrite Us' in BV. split.
               ++ rewrite BT. exact TP.
               ++ intros env v HE Hv. rewrite (BV env v Hv). exact (VP env v HE Hv).
          * cbn [fst snd] in AT, AV. rewrite Us in AV. split.
            -- rewrite TQ. symmetry. exact AT.
            -- intros env v HE Hv. rewrite (VQ env v HE Hv). symmetry. exact (AV env v Hv).
        + exfalso. pose proof (find_none _ _ F2 _ (FWD p b I1)) as E. cbn beta in E.
          cbn [fst] in E. rewrite M1 in E. discriminate.
      - destruct (pickn s t arms') as [[q b'] |] eqn:F2; [| reflexivity]. exfalso.
        destruct (find_some _ _ F2) as [I2 M2]. cbn beta in M2. cbn [fst] in M2.
        destruct (INV q b' I2) as [bq [Iq _]].
        pose proof (find_none _ _ F1 _ Iq) as E. cbn beta in E. cbn [fst] in E.
        rewrite M2 in E. discriminate. }
    split.
    + rewrite !ntype_match, Ta. destruct (ntype s (Gf s) a) as [t |]; [| reflexivity].
      specialize (K t eq_refl). destruct (pickn s t arms) as [[p b] |].
      * destruct K as [q [b' [K1 [K2 _]]]]. rewrite K1. exact K2.
      * rewrite K. reflexivity.
    + intros env HE. rewrite !nseval_match, Ta, (Va env HE).
      destruct (ntype s (Gf s) a) as [t |] eqn:Tt; [| reflexivity].
      destruct (nseval_typed s (Gf s) a t env Tt HE) as [v [Ev Hv]]. rewrite Ev.
      specialize (K t eq_refl). destruct (pickn s t arms) as [[p b] |].
      * destruct K as [q [b' [K1 [_ K3]]]]. rewrite K1. exact (K3 env v HE Hv).
      * rewrite K. reflexivity.
Qed.

(**md
**A body that glues means the same after any rearrangement of its arms.**

Take a body, and the same body with the arms of every match rearranged, at any depth. If both
glue over a set of instantiations, they have the same type at every instantiation in the set,
and on values of the types in scope they return the same value. A match in the body may be glued
by priority, by agreement, or by each on different overlaps.

This is `reordering_arms_changes_nothing` with agreement admitted. The arm selected by a match
may differ between the two bodies, which it cannot under priority alone. The proof follows the
body that runs in each: both are examined at the instantiation, because each is examined
wherever its test succeeds.

- [f:] the rearrangement applied to each list of arms. It keeps the same arms.
- [e:] the body.
- [R:] the instantiations that reach the body.
- [Gf:] the types of the variables in scope at each of them.
*)
Theorem glued_body_means_the_same_reordered
    (f : list (test * ntm) -> list (test * ntm)) (e : ntm)
    (R : list inst3) (Gf : inst3 -> list ty) :
  (forall l a, In a (f l) <-> In a l) ->
  nglued R Gf e -> nglued R Gf (reorder f e) ->
  forall s, In s R ->
    ntype s (Gf s) (reorder f e) = ntype s (Gf s) e /\
    forall env : list val, Forall2 has_ty env (Gf s) ->
      nseval s (Gf s) env (reorder f e) = nseval s (Gf s) env e.
Proof.
  intros Hf N1 N2. exact (glued_reorder_same f Hf e R Gf Gf (fun _ _ => eq_refl) N1 N2).
Qed.

(**md
**A definition that glues may have the arms of any of its matches rearranged.**

For a definition, the gluing condition starts from the whole table. If the definition and its
rearrangement both glue, the rearrangement passes the type check exactly when the definition
does, and at every instantiation that satisfies the constraints the two return the same result
on a scrutinee and arguments of the declared types.

- [G:] the types of the other parameters.
- [e:] the body.
- [res:] the declared result type.
- [f:] the rearrangement applied to each list of arms.
*)
Theorem glued_definition_means_the_same_reordered
    (CA CB : cset) (G : list oty3) (e : ntm) (res : oty3)
    (f : list (test * ntm) -> list (test * ntm)) :
  (forall l a, In a (f l) <-> In a l) ->
  nglued (table CA CB) (top_ctx G) e ->
  nglued (table CA CB) (top_ctx G) (reorder f e) ->
  ncheck CA CB G (reorder f e) res = ncheck CA CB G e res /\
  forall (s : inst3) (env : list val) (x : val),
    valid CA CB s -> has_ty x (iT s) ->
    Forall2 has_ty env (map (inst3ty s) G) ->
    nseval s (iT s :: map (inst3ty s) G) (x :: env) (reorder f e) =
    nseval s (iT s :: map (inst3ty s) G) (x :: env) e.
Proof.
  intros Hf N1 N2.
  pose proof (glued_body_means_the_same_reordered f e (table CA CB) (top_ctx G) Hf N1 N2) as K.
  split.
  - unfold ncheck. apply forallb_eq_in. intros s Hs. destruct (K s Hs) as [T _].
    unfold top_ctx in T. rewrite T. reflexivity.
  - intros s env x V Hx HE. destruct (K s (proj2 (table_iff_valid CA CB s) V)) as [_ E].
    apply E. unfold top_ctx. constructor; assumption.
Qed.

(**md
**The gluing condition accepts in both orders a definition the overlap check rejects.**

For `'A : (x | y)` and `'B : (y)`, the two-arm match whose arms both return the scrutinee glues,
and so does the same match with its arms reversed. The whole-body overlap check rejects it,
because the arms overlap and neither is more specific. So the hypotheses of the two theorems
above can be met by a definition that priority does not admit.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
*)
Theorem gluing_accepts_what_overlap_check_rejects (x y : ty) :
  x <> y ->
  nglued (table [x; y] [y]) (top_ctx []) two_arms /\
  nglued (table [x; y] [y]) (top_ctx []) (reorder (@rev (test * ntm)) two_arms) /\
  nordered (table [x; y] [y]) (top_ctx []) two_arms = false.
Proof.
  intros N. split; [| split].
  - unfold two_arms. cbn [nglued]. split; [exact I |]. split; [| repeat split].
    apply inner_same_body_glues. reflexivity.
  - unfold two_arms. cbn [reorder map rev app fst snd nglued].
    split; [exact I |]. split; [| repeat split].
    apply inner_same_body_glues. reflexivity.
  - destruct (nordered (table [x; y] [y]) (top_ctx []) two_arms) eqn:E; [| reflexivity].
    unfold two_arms in E. apply nordered_match in E. destruct E as [_ [O _]].
    change (ordered_in (table [x; y] [y]) iT [] [IsA; IsB] = true) in O.
    rewrite ordered_in_table, (unordered_overlap_rejected x y N) in O. discriminate.
Qed.

(**md ### How the two whole-body conditions relate

The overlap check of a whole body, `nordered`, and the gluing condition, `nglued`, each give a
theorem on arm order. This section relates them. Neither implies the other. The reason is the
set each hands to an arm's body, and a third condition that changes both the set and the rule
for one match sits between them: every body that passes the overlap check satisfies it, it
admits agreement, and it still makes arm order irrelevant.
*)

(** A type is not a pair with itself as first component. *)
Lemma ty_not_own_pair (t : ty) : forall u : ty, t <> TPair t u.
Proof.
  induction t as [c | a IHa b IHb | a IHa b IHb]; intros u H; try discriminate.
  injection H as H1 _. exact (IHa _ H1).
Qed.

(** Reduce a goal over a table of instantiations built from two different types. *)
Ltac crunch Q1 Q2 :=
  repeat (progress (cbn; try unfold rows; try unfold lt_in; try unfold le_in;
                    rewrite ?tyeqb_refl, ?Q1, ?Q2)).

(** A definition with an intersection arm first, and a match inside the arm `:? 'A` whose second
    arm can never be selected there. *)
Definition shadowed : ntm :=
  NMatch (NVar 0)
    [(Both IsA IsB, NVar 0);
     (IsA, NMatch (NVar 0) [(IsA, NVar 0); (IsB, NPair (NVar 0) (NVar 0))]);
     (IsB, NVar 0)].

(**md
**A body that passes the whole-body overlap check need not satisfy the gluing condition.**

Take `'A : (x | y)` and `'B : (y)`, and the definition

```fsharp
match v with
| :? 'A & :? 'B -> v
| :? 'A as a ->
    match a with
    | :? 'A -> a
    | :? 'B -> (a, a)
| :? 'B -> v
```

It passes the type check with result `'T`, and it passes the whole-body overlap check. The inner
match runs only where `'A` and `'B` differ, because the intersection arm takes the rest, and
there its second arm never succeeds. The gluing condition examines the inner match wherever the
test `:? 'A` of its arm succeeds, which includes the instantiation where the two variables are
the same type. There both inner arms succeed, neither is strictly more specific over that larger
set, and their bodies have different types. So the gluing condition rejects a definition that
priority accepts and whose meaning does not depend on arm order.

With `gluing_accepts_what_overlap_check_rejects`, this makes the two conditions incomparable.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
*)
Theorem ordered_body_glues_falsified (x y : ty) :
  x <> y ->
  ncheck [x; y] [y] [] shadowed VT = true /\
  nordered (table [x; y] [y]) (top_ctx []) shadowed = true /\
  ~ nglued (table [x; y] [y]) (top_ctx []) shadowed.
Proof.
  intros N.
  assert (Q1 : tyeqb x y = false) by (apply tyeqb_false; exact N).
  assert (Q2 : tyeqb y x = false) by (apply tyeqb_false; congruence).
  split; [| split].
  - unfold ncheck, shadowed. crunch Q1 Q2. reflexivity.
  - unfold shadowed. crunch Q1 Q2. reflexivity.
  - intros H. unfold shadowed in H. apply nglued_match in H. destruct H as [_ [_ A]].
    specialize (A IsA _ (or_intror (or_introl eq_refl))).
    apply nglued_match in A. destruct A as [_ [GL _]].
    destruct (GL (Inst y y y) (IsA, NVar 0) (IsB, NPair (NVar 0) (NVar 0))) as [L | [AT _]].
    + crunch Q1 Q2. auto.
    + crunch Q1 Q2. reflexivity.
    + simpl. auto.
    + crunch Q1 Q2. reflexivity.
    + revert L. crunch Q1 Q2. discriminate.
    + revert AT. crunch Q1 Q2. intros AT. injection AT as AT.
      exact (ty_not_own_pair y y AT).
Qed.

(** A property of every arm of a match, given the tests of the arms before it.
    - [P:] the property of one arm, given the tests before it, its test and its body.
    - [seen:] the tests of the arms before the ones considered.
    - [l:] the arms still to consider. *)
Fixpoint arms_all (P : list test -> test -> ntm -> Prop) (seen : list test)
  (l : list (test * ntm)) : Prop :=
  match l with
  | [] => True
  | (p, b) :: r => P seen p b /\ arms_all P (seen ++ [p]) r
  end.

Lemma arms_all_const (Q : test -> ntm -> Prop) (l : list (test * ntm)) :
  forall seen : list test,
    arms_all (fun _ => Q) seen l <-> forall p b, In (p, b) l -> Q p b.
Proof.
  induction l as [| [p0 b0] r IH]; intros seen; cbn [arms_all]; split.
  - intros _ p b [].
  - intros _. exact I.
  - intros [H1 H2] p b [E | Hin].
    + injection E as <- <-. exact H1.
    + exact (proj1 (IH _) H2 p b Hin).
  - intros H. split.
    + apply H. left. reflexivity.
    + apply (proj2 (IH _)). intros p b Hin. apply H. right. exact Hin.
Qed.

(** The gluing condition with each arm's body examined only where the arm is selected, as the
    overlap check of a whole body does. It is stated to be refuted.
    - [R:] the instantiations that reach the body.
    - [Gf:] the types of the variables in scope at each instantiation.
    - [e:] the body. *)
Fixpoint nglued_sel (R : list inst3) (Gf : inst3 -> list ty) (e : ntm) : Prop :=
  match e with
  | NVar _ => True
  | NPrim _ a => nglued_sel R Gf a
  | NPair a b => nglued_sel R Gf a /\ nglued_sel R Gf b
  | NFst a => nglued_sel R Gf a
  | NSnd a => nglued_sel R Gf a
  | NLet a b => nglued_sel R Gf a /\ nglued_sel R (let_ctx Gf a) b
  | NMatch a arms =>
      nglued_sel R Gf a /\
      glues_in R (scrut_ty Gf a) Gf arms /\
      arms_all
        (fun seen p b => nglued_sel (reach R (scrut_ty Gf a) seen p) (arm_ctx Gf p) b)
        [] arms
  end.

(** Two arms of which the first is strictly more specific glue. *)
Lemma first_more_specific_glues
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (p q : test) (b1 b2 : ntm) :
  lt_in R u p q = true -> glues_in R u Gf [(p, b1); (q, b2)].
Proof.
  intros L s a c Hs F Hc M. unfold pickn in F. cbn [find fst] in F.
  destruct (holds s (u s) p) eqn:Hp.
  - injection F as <-. destruct Hc as [<- | [<- | []]].
    + right. apply agree_in_refl.
    + left. exact L.
  - destruct (holds s (u s) q) eqn:Hq; [| discriminate]. injection F as <-.
    destruct Hc as [<- | [<- | []]].
    + cbn [fst] in M. rewrite Hp in M. discriminate.
    + right. apply agree_in_refl.
Qed.

(** Two arms whose tests never both succeed glue. *)
Lemma no_overlap_glues
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (p q : test) (b1 b2 : ntm) :
  (forall s, In s R -> holds s (u s) p && holds s (u s) q = false) ->
  glues_in R u Gf [(p, b1); (q, b2)].
Proof.
  intros H s a c Hs F Hc M. right. destruct (find_some _ _ F) as [Ha Ma]. cbn beta in Ma.
  specialize (H s Hs).
  destruct Ha as [<- | [<- | []]]; destruct Hc as [<- | [<- | []]]; cbn [fst] in Ma, M;
    first [apply agree_in_refl | rewrite Ma, M in H; discriminate].
Qed.

(** A definition with a second parameter of type `'T`. Each outer arm holds the same inner
    match, which returns the scrutinee in one arm and the second parameter in the other. *)
Definition crossed : ntm :=
  NMatch (NVar 0)
    [(IsA, NMatch (NVar 0) [(IsB, NVar 2); (IsA, NVar 3)]);
     (IsB, NMatch (NVar 0) [(IsB, NVar 2); (IsA, NVar 3)])].

(**md
**Under agreement, examining an arm's body only where the arm is selected is unsound.**

Take the gluing condition with the set of the overlap check: the arms of each match glue, and an
arm's body is examined at the instantiations where the arm is selected. For `'A : (x | y)` and
`'B : (y)`, take the definition with a second parameter `w` of type `'T`

```fsharp
match v with
| :? 'A as a -> (match a with :? 'B -> v | :? 'A -> w)
| :? 'B as b -> (match b with :? 'B -> v | :? 'A -> w)
```

and the same definition with the arms of every match reversed. Both satisfy that condition and
both pass the type check with result `'T`. Where `'A` and `'B` are the same type the first
returns `v` and the second returns `w`.

The two outer arms agree in each order, because they hold the same body. The inner match of an
outer arm is ordered by priority over the set where that arm is first, and nothing is asked of it
where the other outer arm is first. After the reversal the roles are exchanged. So in each order
the inner match that runs at the shared instantiation is the one examined there, and the two are
different matches.

This settles the question left open with `nglued`: under agreement as stated there, the smaller
set does not do.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
- [v:] the scrutinee.
- [w:] the second argument.
*)
Theorem selected_set_gluing_falsified (x y : ty) (v w : val) :
  x <> y ->
  nglued_sel (table [x; y] [y]) (top_ctx [VT]) crossed /\
  nglued_sel (table [x; y] [y]) (top_ctx [VT]) (reorder (@rev (test * ntm)) crossed) /\
  ncheck [x; y] [y] [VT] crossed VT = true /\
  ncheck [x; y] [y] [VT] (reorder (@rev (test * ntm)) crossed) VT = true /\
  nseval (Inst y y y) (top_ctx [VT] (Inst y y y)) [v; w] crossed = Some v /\
  nseval (Inst y y y) (top_ctx [VT] (Inst y y y)) [v; w]
    (reorder (@rev (test * ntm)) crossed) = Some w.
Proof.
  intros N.
  assert (Q1 : tyeqb x y = false) by (apply tyeqb_false; exact N).
  assert (Q2 : tyeqb y x = false) by (apply tyeqb_false; congruence).
  split; [| split; [| split; [| split; [| split]]]].
  - unfold crossed. cbn [nglued_sel arms_all app].
    split; [exact I |]. split; [apply inner_same_body_glues; reflexivity |].
    split; [| split; [| exact I]].
    + split; [exact I |]. split; [| repeat split].
      apply first_more_specific_glues. crunch Q1 Q2. reflexivity.
    + split; [exact I |]. split; [| repeat split].
      apply no_overlap_glues. crunch Q1 Q2. intros s [<- | []]. crunch Q1 Q2. reflexivity.
  - unfold crossed. cbn [reorder map rev app fst snd nglued_sel arms_all].
    split; [exact I |]. split; [apply inner_same_body_glues; reflexivity |].
    split; [| split; [| exact I]].
    + split; [exact I |]. split; [| repeat split].
      apply first_more_specific_glues. crunch Q1 Q2. reflexivity.
    + split; [exact I |]. split; [| repeat split].
      apply no_overlap_glues. crunch Q1 Q2. intros s [<- | []]. crunch Q1 Q2. reflexivity.
  - unfold ncheck, crossed. crunch Q1 Q2. reflexivity.
  - unfold ncheck, crossed. crunch Q1 Q2. reflexivity.
  - unfold crossed. crunch Q1 Q2. reflexivity.
  - unfold crossed. crunch Q1 Q2. reflexivity.
Qed.

(**md #### Gluing with priority kept

The two refutations point at one cause. The gluing condition lets two arms agree even when one is
strictly more specific than the other, so the more general arm may be written first and run on
the overlap. Its body then has to be examined on the whole of its test, and that is the larger
set that `ordered_body_glues_falsified` shows to be too large for priority.

The condition below keeps priority where there is one. Of two overlapping arms, if one is
strictly more specific it must be the one selected. Agreement is admitted only between arms of
which neither is strictly more specific. An arm is then never selected where a strictly more
specific arm also succeeds, and its body is examined on the rest of its test. That set is
computed from the tests alone.

The RFC adopts this condition. The [Discussion](Clef.RFC0002.Discussion.html) gives the reasons
and lists agreement between any two overlapping arms among the alternatives.
*)

(** The instantiations of a set at which a test succeeds and no strictly more specific test of
    the match does.
    - [R:] the instantiations the match runs at.
    - [u:] the type of its scrutinee at each instantiation.
    - [tests:] the tests of all the arms of the match.
    - [p:] the test of the arm. *)
Definition unbeaten (R : list inst3) (u : inst3 -> ty) (tests : list test) (p : test)
  : list inst3 :=
  filter
    (fun s =>
       holds s (u s) p
       && forallb (fun q => negb (holds s (u s) q && lt_in R u q p)) tests)
    R.

(** The arms of a match glue with priority kept over a set of instantiations when, at each of
    them, the selected arm is strictly more specific over the set than each other arm that
    matches, or that arm is not strictly more specific than it and the two agree.
    - [R:] the instantiations the match is checked over.
    - [u:] the type of the scrutinee at each of them.
    - [Gf:] the types of the variables in scope at each of them.
    - [arms:] the arms. *)
Definition pglues_in (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty)
  (arms : list (test * ntm)) : Prop :=
  forall (s : inst3) (p q : test * ntm),
    In s R ->
    pickn s (u s) arms = Some p ->
    In q arms -> holds s (u s) (fst q) = true ->
    lt_in R u (fst p) (fst q) = true \/
    (lt_in R u (fst q) (fst p) = false /\ agree_in s (Gf s) (u s) p q).

(** The gluing condition of a whole body with priority kept. The arms of every match glue with
    priority kept, and the body of each arm is examined where the arm's test succeeds and no
    strictly more specific test does.
    - [R:] the instantiations that can reach the body.
    - [Gf:] the types of the variables in scope at each instantiation.
    - [e:] the body. *)
Fixpoint npglued (R : list inst3) (Gf : inst3 -> list ty) (e : ntm) : Prop :=
  match e with
  | NVar _ => True
  | NPrim _ a => npglued R Gf a
  | NPair a b => npglued R Gf a /\ npglued R Gf b
  | NFst a => npglued R Gf a
  | NSnd a => npglued R Gf a
  | NLet a b => npglued R Gf a /\ npglued R (let_ctx Gf a) b
  | NMatch a arms =>
      npglued R Gf a /\
      pglues_in R (scrut_ty Gf a) Gf arms /\
      arms_all
        (fun _ p b =>
           npglued (unbeaten R (scrut_ty Gf a) (map fst arms) p) (arm_ctx Gf p) b)
        [] arms
  end.

(** What the condition consists of at a match. *)
Lemma npglued_match_iff (R : list inst3) (Gf : inst3 -> list ty) (a : ntm)
  (arms : list (test * ntm)) :
  npglued R Gf (NMatch a arms) <->
  npglued R Gf a /\
  pglues_in R (scrut_ty Gf a) Gf arms /\
  forall p b, In (p, b) arms ->
    npglued (unbeaten R (scrut_ty Gf a) (map fst arms) p) (arm_ctx Gf p) b.
Proof.
  cbn [npglued].
  pose proof (arms_all_const
                (fun p b => npglued (unbeaten R (scrut_ty Gf a) (map fst arms) p)
                              (arm_ctx Gf p) b) arms []) as K.
  split; intros [H1 [H2 H3]]; (split; [exact H1 |]); (split; [exact H2 |]).
  - exact (proj1 K H3).
  - exact (proj2 K H3).
Qed.

Lemma lt_in_irrefl (R : list inst3) (u : inst3 -> ty) (p : test) : lt_in R u p p = false.
Proof.
  unfold lt_in. rewrite le_in_refl. reflexivity.
Qed.

(** The comparison of two tests over a set depends only on which instantiations are in it. *)
Lemma le_in_equiv (R R' : list inst3) (u : inst3 -> ty) (p q : test) :
  (forall s, In s R <-> In s R') -> le_in R u p q = le_in R' u p q.
Proof.
  intros E. apply Bool.eq_iff_eq_true. rewrite !le_in_iff.
  split; intros H s Hs; apply H; apply E; exact Hs.
Qed.

Lemma lt_in_equiv (R R' : list inst3) (u : inst3 -> ty) (p q : test) :
  (forall s, In s R <-> In s R') -> lt_in R u p q = lt_in R' u p q.
Proof.
  intros E. unfold lt_in.
  rewrite (le_in_equiv R R' u p q E), (le_in_equiv R R' u q p E). reflexivity.
Qed.

Lemma forallb_members {A : Type} (g : A -> bool) (l1 l2 : list A) :
  (forall x, In x l1 <-> In x l2) -> forallb g l1 = forallb g l2.
Proof.
  intros H. apply Bool.eq_iff_eq_true. rewrite !forallb_forall.
  split; intros K x Hx; apply K; apply H; exact Hx.
Qed.

(** With priority kept, the selected arm is selected where no strictly more specific arm
    succeeds. *)
Lemma selected_unbeaten
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (arms : list (test * ntm))
    (s : inst3) (p : test * ntm) :
  pglues_in R u Gf arms -> In s R -> pickn s (u s) arms = Some p ->
  In s (unbeaten R u (map fst arms) (fst p)).
Proof.
  intros G Hs F. destruct (find_some _ _ F) as [_ Mp]. cbn beta in Mp.
  unfold unbeaten. apply filter_In. split; [exact Hs |]. cbn beta. rewrite Mp. cbn [andb].
  apply forallb_forall. intros r Hr. apply in_map_iff in Hr. destruct Hr as [[r' br] [Er Ir]].
  cbn [fst] in Er. subst r'.
  destruct (holds s (u s) r) eqn:Mr; [| reflexivity]. cbn [andb].
  destruct (lt_in R u r (fst p)) eqn:X; [| reflexivity]. exfalso.
  destruct (G s p (r, br) Hs F Ir Mr) as [L | [L _]]; cbn [fst] in L.
  - exact (lt_in_asym R u _ _ L X).
  - rewrite X in L. discriminate.
Qed.

(** A body that passes the overlap check over a set glues with priority kept over any set with
    the same members. *)
Lemma ordered_glues_over (e : ntm) :
  forall (R R' : list inst3) (Gf : inst3 -> list ty),
    (forall s, In s R <-> In s R') ->
    nordered R Gf e = true -> npglued R' Gf e.
Proof.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | a arms IHa IH]
    using ntm_arms_ind; intros R R' Gf E N.
  - exact I.
  - cbn [nordered] in N. cbn [npglued]. exact (IH R R' Gf E N).
  - cbn [nordered] in N. apply andb_true_iff in N. destruct N as [Na Nb]. cbn [npglued].
    split; [exact (IHa R R' Gf E Na) | exact (IHb R R' Gf E Nb)].
  - cbn [nordered] in N. cbn [npglued]. exact (IH R R' Gf E N).
  - cbn [nordered] in N. cbn [npglued]. exact (IH R R' Gf E N).
  - cbn [nordered] in N. apply andb_true_iff in N. destruct N as [Na Nb]. cbn [npglued].
    split; [exact (IHa R R' Gf E Na) | exact (IHb R R' (let_ctx Gf a) E Nb)].
  - apply nordered_match in N. destruct N as [Na [O [D A]]].
    apply npglued_match_iff. split; [exact (IHa R R' Gf E Na) |].
    remember (scrut_ty Gf a) as u eqn:Eu.
    assert (MS : forall s p q, In s R ->
              find (fun t => holds s (u s) t) (map fst arms) = Some p ->
              In q (map fst arms) -> holds s (u s) q = true -> le_in R u p q = true).
    { intros s p q Hs F Hq M.
      exact (inner_first_match_is_most_specific R u (map fst arms) s p q O Hs F Hq M). }
    split.
    + intros s p q Hs' F Hq M. pose proof (proj2 (E s) Hs') as Hs.
      destruct (find_some _ _ F) as [Hp _].
      assert (L : le_in R u (fst p) (fst q) = true).
      { apply (MS s (fst p) (fst q) Hs).
        - rewrite find_map. unfold pickn in F. rewrite F. reflexivity.
        - apply in_map. exact Hq.
        - exact M. }
      destruct (le_in R u (fst q) (fst p)) eqn:L2.
      * right. assert (PQ : p = q).
        { apply (distinct_fst_inj R u arms D p q Hp Hq).
          apply (distinct_antisym R u (map fst arms) D);
            [apply in_map; exact Hp | apply in_map; exact Hq | exact L | exact L2]. }
        subst q. split; [apply lt_in_irrefl | apply agree_in_refl].
      * left. rewrite <- (lt_in_equiv R R' u (fst p) (fst q) E). unfold lt_in.
        rewrite L, L2. reflexivity.
    + intros p b Ib. destruct (in_split _ _ Ib) as [pre [post Ea]].
      pose proof (A pre p b post Ea) as B.
      rewrite Forall_forall in IH.
      apply (IH (p, b) Ib (reach R u (map fst pre) p) _ (arm_ctx Gf p)); [| exact B].
      assert (NI : ~ In p (map fst pre)).
      { pose proof D as D'. rewrite Ea, map_app in D'. exact (distinct_notin _ _ _ _ _ D'). }
      assert (TE : map fst arms = map fst pre ++ p :: map fst post).
      { rewrite Ea, map_app. reflexivity. }
      assert (Ip : In p (map fst arms)) by (rewrite TE; apply in_elt).
      intros s. unfold reach, unbeaten. rewrite !filter_In. cbn beta. split.
      * intros [Hs H].
        apply (proj1 (reach_pred_iff s (u s) (map fst pre) (map fst post) p NI)) in H.
        rewrite <- TE in H. split; [apply (proj1 (E s)); exact Hs |].
        destruct (find_some _ _ H) as [_ Mp]. cbn beta in Mp. rewrite Mp. cbn [andb].
        apply forallb_forall. intros q Hq. destruct (holds s (u s) q) eqn:Mq; [| reflexivity].
        cbn [andb].
        assert (X : lt_in R' u q p = false).
        { rewrite <- (lt_in_equiv R R' u q p E). unfold lt_in.
          rewrite (MS s p q Hs H Hq Mq). apply andb_false_r. }
        rewrite X. reflexivity.
      * intros [Hs' H]. apply andb_true_iff in H. destruct H as [Mp Hall].
        pose proof (proj2 (E s) Hs') as Hs. split; [exact Hs |].
        apply (proj2 (reach_pred_iff s (u s) (map fst pre) (map fst post) p NI)).
        rewrite <- TE. rewrite forallb_forall in Hall.
        destruct (find (fun q => holds s (u s) q) (map fst arms)) as [p' |] eqn:F.
        -- destruct (find_some _ _ F) as [Ip' Mp']. cbn beta in Mp'.
           assert (L : le_in R u p' p = true) by (exact (MS s p' p Hs F Ip Mp)).
           specialize (Hall p' Ip'). cbn beta in Hall. rewrite Mp' in Hall.
           cbn [andb] in Hall. apply negb_true_iff in Hall.
           rewrite <- (lt_in_equiv R R' u p' p E) in Hall. unfold lt_in in Hall.
           rewrite L in Hall. cbn [andb] in Hall. apply negb_false_iff in Hall.
           f_equal. exact (distinct_antisym R u (map fst arms) D p' p Ip' Ip L Hall).
        -- pose proof (find_none _ _ F p Ip) as Z. cbn beta in Z. rewrite Mp in Z.
           discriminate.
Qed.

(**md
**A body that passes the whole-body overlap check glues with priority kept.**

If a body passes the overlap check over a set of instantiations, it satisfies the gluing
condition with priority kept over the same set. At each match the overlap check gives a selected
arm that is strictly more specific than every other arm that succeeds. And the set the overlap
check hands to an arm's body, where the arm is selected, has the same members as the set this
condition hands to it, where no strictly more specific arm succeeds.

So this condition extends priority, which `nglued` does not.

- [R:] the instantiations that reach the body.
- [Gf:] the types of the variables in scope at each of them.
- [e:] the body.
*)
Theorem ordered_body_glues_with_priority_kept
    (R : list inst3) (Gf : inst3 -> list ty) (e : ntm) :
  nordered R Gf e = true -> npglued R Gf e.
Proof.
  intros N. exact (ordered_glues_over e R R Gf (fun s => iff_refl _) N).
Qed.

(** A body that glues with priority kept, and still does after its arms are rearranged, has the
    same type and, on values of the types in scope, the same value at every instantiation that
    reaches it. The two contexts may differ outside the set. *)
Lemma pglued_reorder_same (f : list (test * ntm) -> list (test * ntm)) :
  (forall l a, In a (f l) <-> In a l) ->
  forall (e : ntm) (R : list inst3) (Gf Gf' : inst3 -> list ty),
    (forall s, In s R -> Gf' s = Gf s) ->
    npglued R Gf e -> npglued R Gf' (reorder f e) ->
    forall s, In s R ->
      ntype s (Gf' s) (reorder f e) = ntype s (Gf s) e /\
      forall env : list val, Forall2 has_ty env (Gf s) ->
        nseval s (Gf' s) env (reorder f e) = nseval s (Gf s) env e.
Proof.
  intros Hf e.
  induction e as [n | o e IH | a b IHa IHb | e IH | e IH | a b IHa IHb | a arms IHa IH]
    using ntm_arms_ind; intros R Gf Gf' HG N1 N2 s Hs.
  - cbn [reorder ntype nseval]. rewrite (HG s Hs). split; [reflexivity | intros; reflexivity].
  - cbn [reorder npglued] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env HE. rewrite (V env HE). reflexivity.
  - cbn [reorder npglued] in N1, N2. destruct N1 as [N1a N1b]. destruct N2 as [N2a N2b].
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    destruct (IHb R Gf Gf' HG N1b N2b s Hs) as [Tb Vb].
    cbn [reorder ntype nseval]. split; [rewrite Ta, Tb; reflexivity |].
    intros env HE. rewrite (Va env HE), (Vb env HE). reflexivity.
  - cbn [reorder npglued] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env HE. rewrite (V env HE). reflexivity.
  - cbn [reorder npglued] in N1, N2. destruct (IH R Gf Gf' HG N1 N2 s Hs) as [T V].
    cbn [reorder ntype nseval]. split; [rewrite T; reflexivity |].
    intros env HE. rewrite (V env HE). reflexivity.
  - cbn [reorder npglued] in N1, N2. destruct N1 as [N1a N1b]. destruct N2 as [N2a N2b].
    assert (HG' : forall s', In s' R -> let_ctx Gf' (reorder f a) s' = let_ctx Gf a s').
    { intros s' Hs'. unfold let_ctx. destruct (IHa R Gf Gf' HG N1a N2a s' Hs') as [T _].
      rewrite T, (HG s' Hs'). reflexivity. }
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    destruct (IHb R (let_ctx Gf a) (let_ctx Gf' (reorder f a)) HG' N1b N2b s Hs) as [Tb Vb].
    unfold let_ctx in Tb, Vb. rewrite Ta in Tb, Vb.
    cbn [reorder ntype nseval]. rewrite Ta.
    destruct (ntype s (Gf s) a) as [x |] eqn:Tx; [| split; [reflexivity | intros; reflexivity]].
    cbn beta iota in Tb, Vb.
    split; [exact Tb |]. intros env HE. rewrite (Va env HE).
    destruct (nseval_typed s (Gf s) a x env Tx HE) as [v [Ev Hv]]. rewrite Ev.
    apply Vb. constructor; assumption.
  - cbn [reorder] in N2. cbn [reorder].
    apply npglued_match_iff in N1. destruct N1 as [N1a [GL1 A1]].
    apply npglued_match_iff in N2. destruct N2 as [N2a [GL2 A2]].
    remember (f (map (fun pb => (fst pb, reorder f (snd pb))) arms)) as arms' eqn:EA.
    assert (U : forall s', In s' R ->
              scrut_ty Gf' (reorder f a) s' = scrut_ty Gf a s').
    { intros s' Hs'. unfold scrut_ty. destruct (IHa R Gf Gf' HG N1a N2a s' Hs') as [T _].
      rewrite T. reflexivity. }
    assert (INV : forall q b', In (q, b') arms' ->
              exists bq, In (q, bq) arms /\ b' = reorder f bq).
    { intros q b' Hin. rewrite EA in Hin. apply (proj1 (Hf _ _)) in Hin.
      apply in_map_iff in Hin.
      destruct Hin as [[py pb] [E Iy]]. cbn [fst snd] in E. injection E as -> <-.
      exists pb. split; [exact Iy | reflexivity]. }
    assert (FWD : forall p b, In (p, b) arms -> In (p, reorder f b) arms').
    { intros p b Hin. rewrite EA. apply (proj2 (Hf _ _)). apply in_map_iff.
      exists (p, b). split; [reflexivity | exact Hin]. }
    assert (TM : forall p, In p (map fst arms) <-> In p (map fst arms')).
    { rewrite EA. apply reorder_tests. exact Hf. }
    assert (REQ : forall p,
              unbeaten R (scrut_ty Gf' (reorder f a)) (map fst arms') p =
              unbeaten R (scrut_ty Gf a) (map fst arms) p).
    { intros p. unfold unbeaten. apply filter_ext_in. intros s' Hs'. cbn beta.
      rewrite (U s' Hs'). apply f_equal.
      rewrite (forallb_members _ (map fst arms') (map fst arms))
        by (intros q; symmetry; apply TM).
      apply forallb_eq. intros q. rewrite (lt_in_ext R _ _ q p U). reflexivity. }
    destruct (IHa R Gf Gf' HG N1a N2a s Hs) as [Ta Va].
    rewrite Forall_forall in IH.
    assert (ARM : forall t p b, ntype s (Gf s) a = Some t -> In (p, b) arms ->
              In s (unbeaten R (scrut_ty Gf a) (map fst arms) p) ->
              ntype s (binder_types s p ++ Gf' s) (reorder f b) =
              ntype s (binder_types s p ++ Gf s) b /\
              forall (env : list val) (v : val), Forall2 has_ty env (Gf s) -> has_ty v t ->
                nseval s (binder_types s p ++ Gf' s) (repeat v (arity p) ++ env) (reorder f b) =
                nseval s (binder_types s p ++ Gf s) (repeat v (arity p) ++ env) b).
    { intros t p b Ht Hin Sin.
      assert (Us : scrut_ty Gf a s = t) by (unfold scrut_ty; rewrite Ht; reflexivity).
      assert (M : holds s t p = true).
      { pose proof Sin as S2. unfold unbeaten in S2. apply filter_In in S2.
        destruct S2 as [_ S2]. cbn beta in S2. apply andb_true_iff in S2.
        destruct S2 as [S2 _]. rewrite Us in S2. exact S2. }
      pose proof (A1 p b Hin) as B1. pose proof (A2 p (reorder f b) (FWD p b Hin)) as B2.
      rewrite REQ in B2.
      assert (HGa : forall s', In s' (unbeaten R (scrut_ty Gf a) (map fst arms) p) ->
                arm_ctx Gf' p s' = arm_ctx Gf p s').
      { intros s' Hs'. unfold unbeaten in Hs'. apply filter_In in Hs'.
        unfold arm_ctx. rewrite (HG s' (proj1 Hs')). reflexivity. }
      destruct (IH (p, b) Hin _ (arm_ctx Gf p) (arm_ctx Gf' p) HGa B1 B2 s Sin) as [T V].
      unfold arm_ctx in T, V. cbn [snd] in T, V. split; [exact T |].
      intros env v HE Hv. apply V. exact (binders_typed s t p v env (Gf s) M Hv HE). }
    assert (K : forall t, ntype s (Gf s) a = Some t ->
              match pickn s t arms with
              | None => pickn s t arms' = None
              | Some (p, b) =>
                  exists q b', pickn s t arms' = Some (q, b') /\
                  ntype s (binder_types s q ++ Gf' s) b' =
                  ntype s (binder_types s p ++ Gf s) b /\
                  forall (env : list val) (v : val), Forall2 has_ty env (Gf s) -> has_ty v t ->
                    nseval s (binder_types s q ++ Gf' s) (repeat v (arity q) ++ env) b' =
                    nseval s (binder_types s p ++ Gf s) (repeat v (arity p) ++ env) b
              end).
    { intros t Ht.
      assert (Us : scrut_ty Gf a s = t) by (unfold scrut_ty; rewrite Ht; reflexivity).
      assert (Us' : scrut_ty Gf' (reorder f a) s = t) by (rewrite (U s Hs); exact Us).
      destruct (pickn s t arms) as [[p b] |] eqn:F1.
      - destruct (find_some _ _ F1) as [I1 M1]. cbn beta in M1. cbn [fst] in M1.
        destruct (pickn s t arms') as [[q b'] |] eqn:F2.
        + destruct (find_some _ _ F2) as [I2 M2]. cbn beta in M2. cbn [fst] in M2.
          destruct (INV q b' I2) as [bq [Iq ->]].
          exists q, (reorder f bq). split; [reflexivity |].
          assert (F1' : pickn s (scrut_ty Gf a s) arms = Some (p, b))
            by (rewrite Us; exact F1).
          assert (M2' : holds s (scrut_ty Gf a s) (fst (q, bq)) = true)
            by (rewrite Us; exact M2).
          assert (F2' : pickn s (scrut_ty Gf' (reorder f a) s) arms' =
                        Some (q, reorder f bq)) by (rewrite Us'; exact F2).
          assert (M1' : holds s (scrut_ty Gf' (reorder f a) s) (fst (p, reorder f b)) = true)
            by (rewrite Us'; exact M1).
          pose proof (selected_unbeaten R _ Gf' arms' s (q, reorder f bq) GL2 Hs F2') as SQ.
          rewrite REQ in SQ. cbn [fst] in SQ.
          destruct (ARM t q bq Ht Iq SQ) as [TQ VQ].
          destruct (GL1 s (p, b) (q, bq) Hs F1' Iq M2') as [L1 | [_ [AT AV]]].
          * exfalso. cbn [fst] in L1.
            destruct (GL2 s (q, reorder f bq) (p, reorder f b) Hs F2' (FWD p b I1) M1')
              as [L2 | [L2 _]];
              rewrite (lt_in_ext R _ _ _ _ U) in L2; cbn [fst] in L2.
            -- exact (lt_in_asym R _ _ _ L1 L2).
            -- rewrite L1 in L2. discriminate.
          * cbn [fst snd] in AT, AV. rewrite Us in AV. split.
            -- rewrite TQ. symmetry. exact AT.
            -- intros env v HE Hv. rewrite (VQ env v HE Hv). symmetry. exact (AV env v Hv).
        + exfalso. pose proof (find_none _ _ F2 _ (FWD p b I1)) as E. cbn beta in E.
          cbn [fst] in E. rewrite M1 in E. discriminate.
      - destruct (pickn s t arms') as [[q b'] |] eqn:F2; [| reflexivity]. exfalso.
        destruct (find_some _ _ F2) as [I2 M2]. cbn beta in M2. cbn [fst] in M2.
        destruct (INV q b' I2) as [bq [Iq _]].
        pose proof (find_none _ _ F1 _ Iq) as E. cbn beta in E. cbn [fst] in E.
        rewrite M2 in E. discriminate. }
    split.
    + rewrite !ntype_match, Ta. destruct (ntype s (Gf s) a) as [t |]; [| reflexivity].
      specialize (K t eq_refl). destruct (pickn s t arms) as [[p b] |].
      * destruct K as [q [b' [K1 [K2 _]]]]. rewrite K1. exact K2.
      * rewrite K. reflexivity.
    + intros env HE. rewrite !nseval_match, Ta, (Va env HE).
      destruct (ntype s (Gf s) a) as [t |] eqn:Tt; [| reflexivity].
      destruct (nseval_typed s (Gf s) a t env Tt HE) as [v [Ev Hv]]. rewrite Ev.
      specialize (K t eq_refl). destruct (pickn s t arms) as [[p b] |].
      * destruct K as [q [b' [K1 [_ K3]]]]. rewrite K1. exact (K3 env v HE Hv).
      * rewrite K. reflexivity.
Qed.

(**md
**A body that glues with priority kept means the same after any rearrangement of its arms.**

Take a body, and the same body with the arms of every match rearranged, at any depth. If both
glue with priority kept over a set of instantiations, they have the same type at every
instantiation in the set, and on values of the types in scope they return the same value.

The arm selected may differ between the two bodies, as under `nglued`. Here the body that runs
in the rearranged match is examined at the instantiation because its arm is selected there, and
a selected arm is never beaten by a strictly more specific one. One of the two bodies is followed
through the rearrangement, and agreement in the original order joins it to the other. The
theorem uses the assumption that every witness is implemented at its declared type, for the
reason `inner_glued_order_irrelevant` gives.

With `ordered_body_glues_with_priority_kept`, this gives the conclusion of
`reordering_arms_changes_nothing` for bodies that pass the overlap check, on values of the types
in scope. That theorem remains the stronger statement for priority alone: it needs no assumption
and holds for every environment.

- [f:] the rearrangement applied to each list of arms. It keeps the same arms.
- [e:] the body.
- [R:] the instantiations that reach the body.
- [Gf:] the types of the variables in scope at each of them.
*)
Theorem priority_kept_body_means_the_same_reordered
    (f : list (test * ntm) -> list (test * ntm)) (e : ntm)
    (R : list inst3) (Gf : inst3 -> list ty) :
  (forall l a, In a (f l) <-> In a l) ->
  npglued R Gf e -> npglued R Gf (reorder f e) ->
  forall s, In s R ->
    ntype s (Gf s) (reorder f e) = ntype s (Gf s) e /\
    forall env : list val, Forall2 has_ty env (Gf s) ->
      nseval s (Gf s) env (reorder f e) = nseval s (Gf s) env e.
Proof.
  intros Hf N1 N2. exact (pglued_reorder_same f Hf e R Gf Gf (fun _ _ => eq_refl) N1 N2).
Qed.

(**md
**A definition that glues with priority kept may have the arms of any of its matches rearranged.**

For a definition, the condition starts from the whole table. If the definition and its
rearrangement both glue with priority kept, the rearrangement passes the type check exactly when
the definition does, and at every instantiation that satisfies the constraints the two return
the same result on a scrutinee and arguments of the declared types.

- [G:] the types of the other parameters.
- [e:] the body.
- [res:] the declared result type.
- [f:] the rearrangement applied to each list of arms.
*)
Theorem priority_kept_definition_means_the_same_reordered
    (CA CB : cset) (G : list oty3) (e : ntm) (res : oty3)
    (f : list (test * ntm) -> list (test * ntm)) :
  (forall l a, In a (f l) <-> In a l) ->
  npglued (table CA CB) (top_ctx G) e ->
  npglued (table CA CB) (top_ctx G) (reorder f e) ->
  ncheck CA CB G (reorder f e) res = ncheck CA CB G e res /\
  forall (s : inst3) (env : list val) (x : val),
    valid CA CB s -> has_ty x (iT s) ->
    Forall2 has_ty env (map (inst3ty s) G) ->
    nseval s (iT s :: map (inst3ty s) G) (x :: env) (reorder f e) =
    nseval s (iT s :: map (inst3ty s) G) (x :: env) e.
Proof.
  intros Hf N1 N2.
  pose proof (priority_kept_body_means_the_same_reordered f e (table CA CB) (top_ctx G)
                Hf N1 N2) as K.
  split.
  - unfold ncheck. apply forallb_eq_in. intros s Hs. destruct (K s Hs) as [T _].
    unfold top_ctx in T. rewrite T. reflexivity.
  - intros s env x V Hx HE. destruct (K s (proj2 (table_iff_valid CA CB s) V)) as [_ E].
    apply E. unfold top_ctx. constructor; assumption.
Qed.

(** Two arms with the same body and the same number of binders, of which neither is strictly more
    specific, glue with priority kept. *)
Lemma incomparable_same_body_glues
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (p q : test) (b : ntm) :
  arity p = arity q ->
  lt_in R u p q = false -> lt_in R u q p = false ->
  pglues_in R u Gf [(p, b); (q, b)].
Proof.
  intros E L1 L2 s a c Hs F Hc M. right. destruct (find_some _ _ F) as [Ha Ma].
  cbn beta in Ma. simpl in Ha, Hc.
  destruct Ha as [<- | [<- | []]]; destruct Hc as [<- | [<- | []]]; cbn [fst] in Ma, M |- *;
    (split;
     [first [apply lt_in_irrefl | exact L1 | exact L2]
     | apply same_body_agrees;
       first [assumption | reflexivity | exact E | symmetry; exact E]]).
Qed.

(**md
**Gluing with priority kept accepts in both orders a definition the overlap check rejects.**

For `'A : (x | y)` and `'B : (y)`, the two-arm match whose arms both return the scrutinee glues
with priority kept, and so does the same match with its arms reversed. Neither test is strictly
more specific than the other over the table, so agreement is admitted, and the two bodies are
the same. The whole-body overlap check rejects the match. So this condition accepts strictly
more than priority, and the hypotheses of the two theorems above can be met by a definition whose
arms are in fact reordered.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
*)
Theorem priority_kept_gluing_accepts_what_overlap_check_rejects (x y : ty) :
  x <> y ->
  npglued (table [x; y] [y]) (top_ctx []) two_arms /\
  npglued (table [x; y] [y]) (top_ctx []) (reorder (@rev (test * ntm)) two_arms) /\
  nordered (table [x; y] [y]) (top_ctx []) two_arms = false.
Proof.
  intros N.
  assert (Q1 : tyeqb x y = false) by (apply tyeqb_false; exact N).
  assert (Q2 : tyeqb y x = false) by (apply tyeqb_false; congruence).
  split; [| split].
  - unfold two_arms. cbn [npglued arms_all]. split; [exact I |]. split; [| repeat split].
    apply incomparable_same_body_glues; [reflexivity | |]; crunch Q1 Q2; reflexivity.
  - unfold two_arms. cbn [reorder map rev app fst snd npglued arms_all].
    split; [exact I |]. split; [| repeat split].
    apply incomparable_same_body_glues; [reflexivity | |]; crunch Q1 Q2; reflexivity.
  - exact (proj2 (proj2 (gluing_accepts_what_overlap_check_rejects x y N))).
Qed.

(**md
**Arms that glue with priority kept glue.**

For one match over one set, gluing with priority kept is the stricter condition. The difference
between the two whole-body conditions is therefore in the set each hands to an arm's body, which
is smaller here.

- [R:] the instantiations the match is checked over.
- [u:] the type of the scrutinee at each of them.
- [Gf:] the types of the variables in scope at each of them.
- [arms:] the arms.
*)
Theorem priority_kept_gluing_glues
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (arms : list (test * ntm)) :
  pglues_in R u Gf arms -> glues_in R u Gf arms.
Proof.
  intros G s p q Hs F Hq M. destruct (G s p q Hs F Hq M) as [L | [_ A]];
    [left; exact L | right; exact A].
Qed.

(**md
**Agreement accepts a match that gluing with priority kept rejects.**

Take the match of `inner_agreement_accepts_what_region_check_rejects`: inside an arm `:? 'A`, on
a scrutinee of type `'T`, the arms `:? 'A` then `:? 'B` with the same body, for `'A : (x | y)`
and `'B : (y)`. In that region `:? 'B` is strictly more specific and is written second. The arms
glue, because the bodies are the same. They do not glue with priority kept, which requires the
strictly more specific arm to be the one selected. What is rejected is a general arm written
before a more specific one that it makes unreachable.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
- [b:] the body both arms have.
- [Gf:] the types of the variables in scope at each instantiation.
*)
Theorem agreement_accepts_what_priority_kept_gluing_rejects
    (x y : ty) (b : ntm) (Gf : inst3 -> list ty) :
  x <> y ->
  glues_in (restrict (table [x; y] [y]) iT IsA) iT Gf [(IsA, b); (IsB, b)] /\
  ~ pglues_in (restrict (table [x; y] [y]) iT IsA) iT Gf [(IsA, b); (IsB, b)].
Proof.
  intros N.
  assert (Q1 : tyeqb x y = false) by (apply tyeqb_false; exact N).
  assert (Q2 : tyeqb y x = false) by (apply tyeqb_false; congruence).
  split; [apply inner_same_body_glues; reflexivity |]. intros G.
  assert (L1 : lt_in (restrict (table [x; y] [y]) iT IsA) iT IsA IsB = false)
    by (crunch Q1 Q2; reflexivity).
  assert (L2 : lt_in (restrict (table [x; y] [y]) iT IsA) iT IsB IsA = true)
    by (crunch Q1 Q2; reflexivity).
  destruct (G (Inst y y y) (IsA, b) (IsB, b)) as [L | [L _]].
  - crunch Q1 Q2. auto.
  - crunch Q1 Q2. reflexivity.
  - simpl. auto.
  - crunch Q1 Q2. reflexivity.
  - cbn [fst] in L. rewrite L1 in L. discriminate.
  - cbn [fst] in L. rewrite L2 in L. discriminate.
Qed.

(**md ## Reporting an arm that can never be selected

An arm can never be selected when, at every instantiation that reaches its match, its test fails
or the test of an earlier arm succeeds. The conditions above accept such an arm. This section
states the report as a computed check and relates it to them.

The check walks the body as the overlap check does. At a match it computes, for each arm, the set
of instantiations at which that arm is selected. An arm whose set is empty is reported. The
arm's body is then walked over that set, so an inner arm is reported when no instantiation that
reaches its match selects it.
*)

(** Whether a set of instantiations has a member. *)
Definition inhabited (l : list inst3) : bool :=
  match l with
  | [] => false
  | _ :: _ => true
  end.

Lemma inhabited_iff (l : list inst3) : inhabited l = true <-> exists s, In s l.
Proof.
  destruct l as [| s l]; simpl; split.
  - discriminate.
  - intros [s []].
  - intros _. exists s. left. reflexivity.
  - reflexivity.
Qed.

(** Whether every arm of one match is selected at some instantiation of a set.
    - [R:] the instantiations the match runs at.
    - [u:] the type of its scrutinee at each instantiation.
    - [arms:] the arms. *)
Definition all_selectable (R : list inst3) (u : inst3 -> ty) (arms : list (test * ntm)) : bool :=
  arms_ok (fun seen p _ => inhabited (reach R u seen p)) [] arms.

(** The report for a whole body. It passes when every arm of every match in the body is selected
    at some instantiation that reaches the match.
    - [R:] the instantiations that reach the body.
    - [Gf:] the types of the variables in scope at each instantiation.
    - [e:] the body. *)
Fixpoint nlive (R : list inst3) (Gf : inst3 -> list ty) (e : ntm) : bool :=
  match e with
  | NVar _ => true
  | NPrim _ a => nlive R Gf a
  | NPair a b => nlive R Gf a && nlive R Gf b
  | NFst a => nlive R Gf a
  | NSnd a => nlive R Gf a
  | NLet a b => nlive R Gf a && nlive R (let_ctx Gf a) b
  | NMatch a arms =>
      nlive R Gf a
      && arms_ok
           (fun seen p b =>
              inhabited (reach R (scrut_ty Gf a) seen p)
              && nlive (reach R (scrut_ty Gf a) seen p) (arm_ctx Gf p) b)
           [] arms
  end.

(** An arm whose test is also the test of an earlier arm is selected nowhere. *)
Lemma reach_none_when_repeated (R : list inst3) (u : inst3 -> ty) (seen : list test) (p : test) :
  In p seen -> reach R u seen p = [].
Proof.
  intros I. unfold reach. induction R as [| s R IH]; [reflexivity |]. cbn [filter].
  destruct (holds s (u s) p) eqn:Hp; cbn [andb]; [| exact IH].
  assert (X : existsb (fun q => holds s (u s) q) seen = true).
  { apply existsb_exists. exists p. split; [exact I | exact Hp]. }
  rewrite X. cbn [negb]. exact IH.
Qed.

(**md
**An arm passes the report exactly when some instantiation selects it.**

For one arm of a match, the computed set has a member if and only if the arm's test is not the
test of an earlier arm and, at some instantiation the match runs at, the match selects that arm.
An arm that repeats an earlier test is always reported. So the report is exact: it names an arm
if and only if no instantiation runs its body.

- [R:] the instantiations the match runs at.
- [u:] the type of its scrutinee at each of them.
- [pre:] the arms before this one.
- [p:] the test of this arm.
- [b:] its body.
- [post:] the arms after it.
*)
Theorem arm_passes_report_iff_selected_somewhere
    (R : list inst3) (u : inst3 -> ty) (pre : list (test * ntm)) (p : test) (b : ntm)
    (post : list (test * ntm)) :
  inhabited (reach R u (map fst pre) p) = true <->
  ~ In p (map fst pre) /\
  exists s, In s R /\ pickn s (u s) (pre ++ (p, b) :: post) = Some (p, b).
Proof.
  rewrite inhabited_iff. split.
  - intros [s Hs].
    assert (NI : ~ In p (map fst pre)).
    { intros I. rewrite (reach_none_when_repeated R u _ p I) in Hs. exact Hs. }
    split; [exact NI |]. exists s.
    exact (proj1 (reach_is_where_the_arm_is_selected R u pre p b post s NI) Hs).
  - intros [NI [s Hs]]. exists s.
    exact (proj2 (reach_is_where_the_arm_is_selected R u pre p b post s NI) Hs).
Qed.

(**md
**In a body that passes the report, every arm of a match is selected somewhere.**

If a match passes the report over a set of instantiations, each of its arms is selected by the
match at some instantiation of the set, and the arm's body passes the report over the set of
instantiations at which the arm is selected. By `reach_is_where_the_arm_is_selected` that set
holds exactly the instantiations at which the body runs, so the statement applies again to a
match inside the body.

- [R:] the instantiations that reach the match.
- [Gf:] the types of the variables in scope at each of them.
- [a:] the scrutinee.
- [arms:] the arms.
- [pre:] the arms before the one considered.
- [p:] its test.
- [b:] its body.
- [post:] the arms after it.
*)
Theorem body_that_passes_report_has_every_arm_selected
    (R : list inst3) (Gf : inst3 -> list ty) (a : ntm) (arms : list (test * ntm))
    (pre : list (test * ntm)) (p : test) (b : ntm) (post : list (test * ntm)) :
  nlive R Gf (NMatch a arms) = true ->
  arms = pre ++ (p, b) :: post ->
  (exists s, In s R /\ pickn s (scrut_ty Gf a s) arms = Some (p, b)) /\
  nlive (reach R (scrut_ty Gf a) (map fst pre) p) (arm_ctx Gf p) b = true.
Proof.
  cbn [nlive]. intros H E. apply andb_true_iff in H. destruct H as [_ H]. rewrite E in H.
  pose proof (arms_ok_split _ pre [] p b post H) as K. cbn [app] in K.
  apply andb_true_iff in K. destruct K as [K1 K2]. split; [| exact K2].
  rewrite E.
  exact (proj2 (proj1 (arm_passes_report_iff_selected_somewhere
                         R (scrut_ty Gf a) pre p b post) K1)).
Qed.

(**md ### The report and the two agreement rules

`agreement_accepts_what_priority_kept_gluing_rejects` gives a match that glues and does not glue
with priority kept, and its second arm can never be selected. The next theorem shows that this
is the only way the two rules differ on one match.
*)

Lemma find_split {A : Type} (f : A -> bool) (l : list A) (x : A) :
  find f l = Some x ->
  exists pre post, l = pre ++ x :: post /\ forall y, In y pre -> f y = false.
Proof.
  induction l as [| a l IH]; simpl; [discriminate |].
  destruct (f a) eqn:Fa.
  - intros E. injection E as <-. exists [], l. split; [reflexivity | intros y []].
  - intros E. destruct (IH E) as [pre [post [-> K]]]. exists (a :: pre), post.
    split; [reflexivity |]. intros y [<- | Hy]; [exact Fa | exact (K y Hy)].
Qed.

(**md
**A match that glues and has no arm to report glues with priority kept.**

Take a match whose arms glue over a set of instantiations, and suppose every arm is selected
somewhere in the set. Then the arms glue with priority kept. The reason is that a later arm
strictly more specific than the selected one would succeed only where the selected one's test
does, and so could never be selected.

With `priority_kept_gluing_glues`, the two agreement rules accept the same matches among those
with no arm to report. What agreement between any two overlapping arms accepts beyond the adopted
rule is a match with an arm that can never be selected.

- [R:] the instantiations the match is checked over.
- [u:] the type of the scrutinee at each of them.
- [Gf:] the types of the variables in scope at each of them.
- [arms:] the arms.
*)
Theorem glued_match_with_no_arm_to_report_keeps_priority
    (R : list inst3) (u : inst3 -> ty) (Gf : inst3 -> list ty) (arms : list (test * ntm)) :
  glues_in R u Gf arms -> all_selectable R u arms = true -> pglues_in R u Gf arms.
Proof.
  intros G L s p q Hs F Hq M.
  destruct (G s p q Hs F Hq M) as [X | A]; [left; exact X |]. right. split; [| exact A].
  destruct (lt_in R u (fst q) (fst p)) eqn:X; [exfalso | reflexivity].
  unfold lt_in in X. apply andb_true_iff in X. destruct X as [X1 X2].
  apply negb_true_iff in X2.
  unfold pickn in F. destruct (find_split _ _ _ F) as [pre [post [E K]]].
  rewrite E in Hq. apply in_app_or in Hq. destruct Hq as [Hq | [<- | Hq]].
  - pose proof (K q Hq) as Z. cbn beta in Z. rewrite Z in M. discriminate.
  - rewrite le_in_refl in X2. discriminate.
  - apply in_split in Hq. destruct Hq as [m [post2 E2]]. destruct q as [tq bq].
    cbn [fst] in X1, M.
    assert (E3 : arms = (pre ++ p :: m) ++ (tq, bq) :: post2).
    { rewrite E, E2, <- app_assoc. reflexivity. }
    unfold all_selectable in L. rewrite E3 in L.
    pose proof (arms_ok_split _ (pre ++ p :: m) [] tq bq post2 L) as Z. cbn [app] in Z.
    apply inhabited_iff in Z. destruct Z as [s' Hs'].
    unfold reach in Hs'. apply filter_In in Hs'. destruct Hs' as [HR HP].
    apply andb_true_iff in HP. destruct HP as [Hq' Hn]. apply negb_true_iff in Hn.
    assert (Y : existsb (fun r => holds s' (u s') r) (map fst (pre ++ p :: m)) = true).
    { apply existsb_exists. exists (fst p). split.
      - apply (in_map fst). apply in_elt.
      - exact (proj1 (le_in_iff R u tq (fst p)) X1 s' HR Hq'). }
    rewrite Y in Hn. discriminate.
Qed.

(**md
**The match that separates the two agreement rules is reported.**

In the match of `agreement_accepts_what_priority_kept_gluing_rejects`, the arm `:? 'B` is written
after `:? 'A` inside a region where `'T` is `'A`. The report names it: no instantiation of the
region selects it.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
- [b:] the body both arms have.
*)
Theorem general_arm_first_is_reported (x y : ty) (b : ntm) :
  x <> y ->
  all_selectable (restrict (table [x; y] [y]) iT IsA) iT [(IsA, b); (IsB, b)] = false.
Proof.
  intros N.
  assert (Q1 : tyeqb x y = false) by (apply tyeqb_false; exact N).
  assert (Q2 : tyeqb y x = false) by (apply tyeqb_false; congruence).
  unfold all_selectable. crunch Q1 Q2. reflexivity.
Qed.

(**md ### The report is a check of its own

Neither the overlap check nor gluing with priority kept implies the report. Each accepts a body
with an arm that can never be selected.
*)

(**md
**The overlap check accepts a body with an arm that can never be selected.**

The definition of `ordered_body_glues_falsified`, for `'A : (x | y)` and `'B : (y)`, passes the
type check and the whole-body overlap check. Its inner match runs only where `'A` and `'B`
differ, and there the inner arm `:? 'B` never succeeds. The report rejects the definition.

- [x:] a member of the first set only.
- [y:] the member the two sets share.
*)
Theorem overlap_check_accepts_an_arm_never_selected (x y : ty) :
  x <> y ->
  ncheck [x; y] [y] [] shadowed VT = true /\
  nordered (table [x; y] [y]) (top_ctx []) shadowed = true /\
  nlive (table [x; y] [y]) (top_ctx []) shadowed = false.
Proof.
  intros N.
  destruct (ordered_body_glues_falsified x y N) as [H1 [H2 _]].
  split; [exact H1 |]. split; [exact H2 |].
  assert (Q1 : tyeqb x y = false) by (apply tyeqb_false; exact N).
  assert (Q2 : tyeqb y x = false) by (apply tyeqb_false; congruence).
  unfold shadowed. crunch Q1 Q2. reflexivity.
Qed.

(** A match whose two arms have the same test and the same body. *)
Definition twice : ntm := NMatch (NVar 0) [(IsA, NVar 0); (IsA, NVar 0)].

(**md
**Gluing with priority kept accepts a body with an arm that can never be selected.**

Take the match with the arm `:? 'A` written twice with one body. For every pair of member sets it
glues with priority kept: neither test is strictly more specific than the other, and the bodies
are the same. Its second arm is selected nowhere, and the report rejects it. The whole-body
overlap check rejects it too, because the two tests are equally specific.

- [CA:] the members of `'A`.
- [CB:] the members of `'B`.
*)
Theorem priority_kept_gluing_accepts_an_arm_never_selected (CA CB : cset) :
  npglued (table CA CB) (top_ctx []) twice /\
  nlive (table CA CB) (top_ctx []) twice = false.
Proof.
  split.
  - unfold twice. cbn [npglued arms_all]. split; [exact I |]. split; [| repeat split].
    apply incomparable_same_body_glues; [reflexivity | |]; apply lt_in_irrefl.
  - unfold twice. cbn [nlive arms_ok app].
    rewrite (reach_none_when_repeated _ _ [IsA] IsA (or_introl eq_refl)).
    cbn [inhabited andb]. apply andb_false_r.
Qed.

(**md ### What the report gives the overlap check

The whole-body overlap check asks two things of a match: that it is ordered, and that no two of
its arms are equally specific. `check_accepts_both_orders` shows the second is needed. The report
implies it.
*)

Lemma selectable_distinct (R : list inst3) (u : inst3 -> ty) :
  forall (arms : list (test * ntm)) (seen : list test),
    arms_ok (fun seen p _ => inhabited (reach R u seen p)) seen arms = true ->
    distinct_in R u (map fst arms) = true.
Proof.
  induction arms as [| [p b] r IH]; intros seen H; [reflexivity |].
  cbn [arms_ok] in H. apply andb_true_iff in H. destruct H as [_ H].
  cbn [map fst distinct_in]. apply andb_true_iff. split; [| exact (IH _ H)].
  apply forallb_forall. intros q Hq. apply negb_true_iff.
  destruct (le_in R u q p) eqn:L2; [exfalso | apply andb_false_r].
  apply in_map_iff in Hq. destruct Hq as [[q' bq] [Eq Iq]]. cbn [fst] in Eq. subst q'.
  apply in_split in Iq. destruct Iq as [m [post E]]. rewrite E in H.
  pose proof (arms_ok_split _ m (seen ++ [p]) q bq post H) as Z. cbn beta in Z.
  apply inhabited_iff in Z. destruct Z as [s Hs]. unfold reach in Hs. apply filter_In in Hs.
  destruct Hs as [HR HP]. apply andb_true_iff in HP. destruct HP as [Hq Hn].
  apply negb_true_iff in Hn.
  assert (Y : existsb (fun t => holds s (u s) t) ((seen ++ [p]) ++ map fst m) = true).
  { apply existsb_exists. exists p. split.
    - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
    - exact (proj1 (le_in_iff R u q p) L2 s HR Hq). }
  rewrite Y in Hn. discriminate.
Qed.

(**md
**A match with no arm to report has no two arms equally specific.**

If every arm of a match is selected somewhere in a set of instantiations, then no later arm is
at least as specific over the set as an earlier one, and in particular no two arms are equally
specific. So for one match the report supplies the second requirement of the whole-body overlap
check.

- [R:] the instantiations the match runs at.
- [u:] the type of its scrutinee at each of them.
- [arms:] the arms.
*)
Theorem match_with_no_arm_to_report_has_distinct_tests
    (R : list inst3) (u : inst3 -> ty) (arms : list (test * ntm)) :
  all_selectable R u arms = true -> distinct_in R u (map fst arms) = true.
Proof.
  intros H. exact (selectable_distinct R u arms [] H).
Qed.

(**md ## Rules stated in prose

These parts of a nested type-case are not modelled.

1. **The gluing conditions are not computed checks.** `nglued` and `npglued` are statements,
   because agreement of two bodies is not decidable in general. A compiler would decide it by
   priority, by identical bodies (`inner_same_body_glues`, `incomparable_same_body_glues`), or by
   a proof it is given. For `npglued` the overlap check is such a procedure
   (`ordered_body_glues_with_priority_kept`), and the set handed to each arm's body is computed.
   No procedure that also decides agreement is modelled.
2. **A whole body that separates the two gluing conditions in the other direction.** A body that
   passes the overlap check glues with priority kept and need not glue
   (`ordered_body_glues_falsified`). That some whole body glues and does not glue with priority
   kept is proved for one match over a given region
   (`agreement_accepts_what_priority_kept_gluing_rejects`), and is not stated for a definition
   checked from the whole table.
3. **Whether the set of `npglued` is the smallest that is sound.** An arm's body is examined
   where its test succeeds and no strictly more specific test does. Where the arm is selected is
   too small under `nglued` (`selected_set_gluing_falsified`). Whether it would do under
   `npglued` is not settled.
4. **Agreement here and in Bodies.** Agreement of two inner arms includes the type of the two
   bodies. Agreement in Bodies does not, because its check types every arm that matches. That
   the first follows from the second for a match with no nesting is not proved.
5. **Every matching arm.** This module types the arm selected at each instantiation. Bodies types
   every arm that matches. The results on arm order do not need the stronger check: under
   priority the same arm is selected in either order, and agreement asks for equal types.
6. **What the report leaves open.** `nlive` names an arm that no instantiation selects. It is a
   check apart from `ncheck`, `nordered` and `npglued`, and no theorem joins them into one check
   of a definition. Whether a reported arm is an error or a warning is not decided. The spec
   gives a warning for a rule that is never matched ([Dynamic Type-test Patterns](https://clef-lang.com/spec/draft/patterns/#dynamic-type-test-patterns)).
   Three statements about the report are not proved. The first is that a body which passes
   `nordered` and the report passes the report after its arms are rearranged. The second is the
   same for a body that glues with priority kept, where the set an arm's body is walked over
   depends on which of two agreeing arms is written first. The third is the whole-body form of
   `glued_match_with_no_arm_to_report_keeps_priority`: the two gluing conditions hand different
   sets to an arm's body, so the statement for one match does not carry to a body.
   `inner_tests_decided_in_a_region` shows when an inner arm is reported for a scrutinee of
   variable type.
7. **The cost of the check.** The check filters the set once for each arm of each match. No bound
   on that work is stated.
*)
