From Stdlib Require Import List ZArith QArith Qpower String Bool Lia.
Import ListNotations.
From Clef Require Import RFC0003.Measures RFC0003.Conversion.

(**md # Inserting conversions

This module models the step the RFC adds to the compiler. A source expression may hold a position
that expects one measure and is given another of the same dimension. The compiler inserts a
scaling there, and erases the measures as it does today.

```fsharp
let speed (d: float<m>) (t: float<s>) = d / t

let v = speed 12.0<km> 0.5<h>      // d is scaled by 1000, t by 3600
```

The position that expects a measure is written `SAs` in the model. It stands for an argument
against a declared parameter, a type annotation and a declared return type. A parameter written
`distance<km>`, which accepts any length and holds it in `km`, is such a position.

The model has rational literals, addition, multiplication, division and that position. It has no
variables and no functions, so a call is represented by the positions of its arguments.
*)

Open Scope Q_scope.

(**md ## Source and target *)

(** A source expression. Every literal carries its measure. *)
Inductive sterm : Type :=
| SLit (q : Q) (m : measure)
| SAdd (a b : sterm)
| SMul (a b : sterm)
| SDiv (a b : sterm)
| SAs (m : measure) (e : sterm).

(** A target expression. Measures are erased, and `TScale` is the inserted scaling. *)
Inductive tterm : Type :=
| TLit (q : Q)
| TAdd (a b : tterm)
| TMul (a b : tterm)
| TDiv (a b : tterm)
| TScale (k : Q) (t : tterm).

(** The number a target expression computes. *)
Fixpoint run (t : tterm) : Q :=
  match t with
  | TLit q => q
  | TAdd a b => run a + run b
  | TMul a b => run a * run b
  | TDiv a b => run a / run b
  | TScale k t => k * run t
  end.

(**md ## What a source expression means

The meaning of a source expression is the quantity it denotes in base units. It is defined on the
source alone and does not mention conversion: a position that expects a measure does not change
the quantity.
*)

(** The quantity a source expression denotes, in base units.
    - [D:] the unit declarations. *)
Fixpoint mean (D : decls) (e : sterm) : Q :=
  match e with
  | SLit q m => q * scale D m
  | SAdd a b => mean D a + mean D b
  | SMul a b => mean D a * mean D b
  | SDiv a b => mean D a / mean D b
  | SAs _ e => mean D e
  end.

(** The dimension of the quantity a source expression denotes. *)
Fixpoint sdim (D : decls) (e : sterm) : measure :=
  match e with
  | SLit _ m => dim D m
  | SAdd a _ => sdim D a
  | SMul a b => mmul (sdim D a) (sdim D b)
  | SDiv a b => mdiv (sdim D a) (sdim D b)
  | SAs _ e => sdim D e
  end.

(**md ## Elaboration

Elaboration checks an expression, computes its measure, and produces the target expression.

- Addition requires equal measures. No conversion is inserted between the operands of an operator,
  since neither operand's measure is the expected one.
- A position that expects a measure accepts any convertible measure. If the two measures are
  equal nothing is inserted; otherwise the value is scaled by the conversion factor.
- A position given a measure of another dimension is an error.
*)

(** The target expression and measure of a source expression, or `None` when it does not check. *)
Fixpoint elab (D : decls) (e : sterm) : option (tterm * measure) :=
  match e with
  | SLit q m => Some (TLit q, m)
  | SAdd a b =>
      match elab D a, elab D b with
      | Some (ta, ma), Some (tb, mb) =>
          if meqb ma mb then Some (TAdd ta tb, ma) else None
      | _, _ => None
      end
  | SMul a b =>
      match elab D a, elab D b with
      | Some (ta, ma), Some (tb, mb) => Some (TMul ta tb, mmul ma mb)
      | _, _ => None
      end
  | SDiv a b =>
      match elab D a, elab D b with
      | Some (ta, ma), Some (tb, mb) => Some (TDiv ta tb, mdiv ma mb)
      | _, _ => None
      end
  | SAs m e =>
      match elab D e with
      | Some (t, a) =>
          if convb D a m
          then Some (if meqb a m then t else TScale (cfactor D a m) t, m)
          else None
      | None => None
      end
  end.

(**md
**Inserted conversions preserve the meaning of the program.**

If an expression checks, the number its target computes, read in the measure the checker gave it,
is the quantity the source denotes. The target carries no measures, so this is the statement that
erasing measures stays sound once conversions are inserted.

The quantity is exact here because the model computes with rationals. A floating-point target
computes an approximation of it.

- [t:] the target expression.
- [m:] the measure the checker gives the expression.
*)
Theorem elab_preserves_meaning (D : decls) (e : sterm) (t : tterm) (m : measure) :
  elab D e = Some (t, m) -> run t * scale D m == mean D e.
Proof.
  revert t m. induction e as [q n | a IHa b IHb | a IHa b IHb | a IHa b IHb | n e IH];
    intros t m H; simpl in H.
  - inversion H; subst. simpl. reflexivity.
  - destruct (elab D a) as [[ta ma] |]; [| discriminate].
    destruct (elab D b) as [[tb mb] |]; [| discriminate].
    destruct (meqb ma mb) eqn:E; [| discriminate]. inversion H; subst. simpl.
    apply meqb_iff in E.
    rewrite <- (IHa ta m eq_refl), <- (IHb tb mb eq_refl), (scale_meq D m mb E). ring.
  - destruct (elab D a) as [[ta ma] |]; [| discriminate].
    destruct (elab D b) as [[tb mb] |]; [| discriminate].
    inversion H; subst. simpl.
    rewrite <- (IHa ta ma eq_refl), <- (IHb tb mb eq_refl), scale_mul. ring.
  - destruct (elab D a) as [[ta ma] |]; [| discriminate].
    destruct (elab D b) as [[tb mb] |]; [| discriminate].
    inversion H; subst. simpl.
    rewrite <- (IHa ta ma eq_refl), <- (IHb tb mb eq_refl), scale_div.
    unfold Qdiv. rewrite Qinv_mult_distr. ring.
  - destruct (elab D e) as [[t0 a] |]; [| discriminate].
    destruct (convb D a n) eqn:C; [| discriminate]. inversion H; subst. simpl.
    rewrite <- (IH t0 a eq_refl). destruct (meqb a m) eqn:E.
    + apply meqb_iff in E. rewrite (scale_meq D a m E). reflexivity.
    + simpl. unfold cfactor. field. apply scale_nonzero.
Qed.

(**md
**A conversion never changes the dimension of a quantity.**

The measure the checker gives an expression has the dimension of the quantity the source denotes.
A length stays a length through every position it passes, whatever unit each position expects.
*)
Theorem elab_keeps_dimension (D : decls) (e : sterm) (t : tterm) (m : measure) :
  elab D e = Some (t, m) -> meq (dim D m) (sdim D e).
Proof.
  revert t m. induction e as [q n | a IHa b IHb | a IHa b IHb | a IHa b IHb | n e IH];
    intros t m H; simpl in H.
  - inversion H; subst. apply meq_refl.
  - destruct (elab D a) as [[ta ma] |]; [| discriminate].
    destruct (elab D b) as [[tb mb] |]; [| discriminate].
    destruct (meqb ma mb); [| discriminate]. inversion H; subst. simpl.
    apply (IHa ta m eq_refl).
  - destruct (elab D a) as [[ta ma] |]; [| discriminate].
    destruct (elab D b) as [[tb mb] |]; [| discriminate].
    inversion H; subst. simpl. eapply meq_trans; [apply dim_mul |].
    apply mmul_meq; [apply (IHa ta ma eq_refl) | apply (IHb tb mb eq_refl)].
  - destruct (elab D a) as [[ta ma] |]; [| discriminate].
    destruct (elab D b) as [[tb mb] |]; [| discriminate].
    inversion H; subst. simpl. unfold mdiv, minv. eapply meq_trans; [apply dim_mul |].
    apply mmul_meq; [apply (IHa ta ma eq_refl) |].
    eapply meq_trans; [apply dim_pow |]. apply mpow_meq. apply (IHb tb mb eq_refl).
  - destruct (elab D e) as [[t0 a] |]; [| discriminate].
    destruct (convb D a n) eqn:C; [| discriminate]. inversion H; subst. simpl.
    apply convb_iff in C. eapply meq_trans; [apply meq_sym; exact C |].
    apply (IH t0 a eq_refl).
Qed.

(**md
**Two expressions with the same meaning and measure compute the same number.**

If two expressions check at equal measures and denote the same quantity, their targets compute the
same number. Which positions a value passed through on the way, and which units they expected,
does not show in the result.
*)
Theorem elab_path_independent (D : decls) (e1 e2 : sterm) (t1 t2 : tterm) (m1 m2 : measure) :
  elab D e1 = Some (t1, m1) -> elab D e2 = Some (t2, m2) ->
  meq m1 m2 -> mean D e1 == mean D e2 ->
  run t1 == run t2.
Proof.
  intros H1 H2 E M.
  apply elab_preserves_meaning in H1. apply elab_preserves_meaning in H2.
  rewrite <- H1, <- H2, (scale_meq D m1 m2 E) in M.
  apply (Qmult_inj_r _ _ (scale D m2)); [apply scale_nonzero | exact M].
Qed.

(**md
**Converting through an intermediate unit gives the same number as converting directly.**

A value that passes a position expecting `b` and then one expecting `c` computes the same number
as a value passed straight to the position expecting `c`. The compiler may therefore fuse two
adjacent scalings into one, or drop the intermediate one.

- [b:] the intermediate measure.
- [c:] the final measure.
*)
Theorem elab_fuses (D : decls) (e : sterm) (b c : measure) (t1 t2 : tterm) (m1 m2 : measure) :
  elab D (SAs c (SAs b e)) = Some (t1, m1) -> elab D (SAs c e) = Some (t2, m2) ->
  run t1 == run t2.
Proof.
  intros H1 H2. assert (E : m1 = c /\ m2 = c).
  { simpl in H1, H2. destruct (elab D e) as [[t0 a] |]; [| discriminate].
    destruct (convb D a b); [| discriminate]. destruct (convb D b c); [| discriminate].
    destruct (convb D a c); [| discriminate]. inversion H1; inversion H2; subst; split; reflexivity. }
  destruct E as [-> ->].
  apply (elab_path_independent D _ _ _ _ c c H1 H2); [apply meq_refl | reflexivity].
Qed.

(**md ## An example *)

Open Scope string_scope.

(** `12.0<km> / 0.5<h>` passed to a position that expects `m/s`. *)
Definition ex_speed : sterm :=
  SAs ms (SDiv (SLit 12 [("km", 1%Z)]) (SLit (1 # 2) [("h", 1%Z)])).

(** The example checks at `m/s`, and its target computes 20/3, which is 24 km/h in m/s. *)
Lemma ex_speed_runs :
  exists t, elab ex ex_speed = Some (t, ms) /\ Qred (run t) = 20 # 3.
Proof.
  eexists. split; vm_compute; reflexivity.
Qed.

(** A length passed to a position that expects a time does not check. *)
Lemma ex_length_as_time : elab ex (SAs [("s", 1%Z)] (SLit 1 [("km", 1%Z)])) = None.
Proof.
  vm_compute. reflexivity.
Qed.
