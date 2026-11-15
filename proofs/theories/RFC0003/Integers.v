From Stdlib Require Import List ZArith QArith Qpower Qround String Bool Lia Lqa.
Import ListNotations.
From Clef Require Import RFC0003.Measures RFC0003.Conversion.

(**md # Integers

A rational value converts between any two convertible measures. An integer does not: 3 `km` is
3000 `m`, but 1500 `m` is not a whole number of `km`. This module works out what that means for
the design.

- An integer conversion is *exact* when the factor is a whole number, and the compiler can decide
  that.
- Exact conversion orders the units of a dimension from coarse to fine. Where `km` meets `m` in
  one integer expression, the expression is inferred at `m`, the finer of the two.
- A conversion that is not exact loses resolution. A position may accept that, as a parameter
  `distance<km>` given an integer in `m` does, and the loss is then less than one unit of the
  target. A position that has not accepted it is an error.

Integers here are unbounded. Overflow of a fixed-width integer is not modelled.
*)

Open Scope Q_scope.

(**md ## Exact conversion *)

(** The integer a rational is equal to, when it is equal to one. *)
Definition qint (q : Q) : option Z :=
  let n := (Qnum q / Zpos (Qden q))%Z in
  if Qeq_bool (inject_Z n) q then Some n else None.

(** The computed integer is the rational's value, and every integer value is found. *)
Lemma qint_iff (q : Q) (n : Z) : qint q = Some n <-> q == inject_Z n.
Proof.
  unfold qint. split.
  - destruct (Qeq_bool _ q) eqn:E; [| discriminate]. intro H. inversion H; subst.
    apply Qeq_bool_iff in E. symmetry. exact E.
  - intro H. assert (N : (Qnum q / Zpos (Qden q))%Z = n).
    { unfold Qeq in H. simpl in H. rewrite Z.mul_1_r in H. rewrite H.
      apply Z.div_mul. discriminate. }
    rewrite N. assert (B : Qeq_bool (inject_Z n) q = true).
    { apply Qeq_bool_iff. symmetry. exact H. }
    rewrite B. reflexivity.
Qed.

(** The whole-number factor from one measure to another, when there is one.
    - [a:] the measure converted from.
    - [b:] the measure converted to. *)
Definition int_factor (D : decls) (a b : measure) : option Z := qint (cfactor D a b).

(**md
**Whether an integer conversion is exact is decidable.**

The computed factor is `Some n` exactly when one of the source measure is `n` of the target. The
compiler can therefore tell, from the declarations alone, whether every integer in the source
measure is a whole number of the target.
*)
Theorem int_factor_iff (D : decls) (a b : measure) (n : Z) :
  int_factor D a b = Some n <-> scale D a == inject_Z n * scale D b.
Proof.
  unfold int_factor. rewrite qint_iff. unfold cfactor.
  pose proof (scale_nonzero D b) as Nz. split; intro H.
  - rewrite <- H. field. exact Nz.
  - rewrite H. field. exact Nz.
Qed.

(**md
**Where no whole-number factor exists, some integer cannot be converted.**

If the computed factor is `None`, one unit of the source measure is not a whole number of the
target. So `m` to `km` is not an exact conversion for integers, while `km` to `m` is.
*)
Theorem int_factor_none (D : decls) (a b : measure) :
  int_factor D a b = None -> ~ exists z, scale D a == inject_Z z * scale D b.
Proof.
  intros H [z E]. apply int_factor_iff in E. congruence.
Qed.

(** One measure converts exactly to another: they are convertible and the factor is whole. *)
Definition int_conv (D : decls) (a b : measure) : Prop :=
  conv D a b /\ exists n, scale D a == inject_Z n * scale D b.

(**md
**Exact conversion orders the units of a dimension from coarse to fine.**

Every measure converts exactly to itself, and exact conversions compose. If two measures convert
exactly to each other they have the same size. The relation is therefore an order on sizes, and
it points from the coarser measure to the finer one.
*)
Theorem int_conv_order (D : decls) (a b c : measure) :
  int_conv D a a /\
  (int_conv D a b -> int_conv D b c -> int_conv D a c) /\
  (int_conv D a b -> int_conv D b a -> scale D a == scale D b).
Proof.
  unfold int_conv. split; [| split].
  - split; [apply meq_refl |]. exists 1%Z. ring.
  - intros [C1 [n Hn]] [C2 [k Hk]]. split; [exact (meq_trans _ _ _ C1 C2) |].
    exists (n * k)%Z. rewrite Hn, Hk, inject_Z_mult. ring.
  - intros [_ [n Hn]] [_ [k Hk]].
    pose proof (scale_pos D a) as Pa. pose proof (scale_pos D b) as Pb.
    assert (E : inject_Z (n * k) * scale D a == 1 * scale D a).
    { rewrite inject_Z_mult. rewrite Hk in Hn at 1. rewrite Hn at 2. ring. }
    apply Qmult_inj_r in E; [| apply scale_nonzero].
    unfold Qeq in E. simpl in E. rewrite Z.mul_1_r in E.
    destruct (Z.eq_mul_1 n k E) as [-> | ->].
    + rewrite Hn. ring.
    + exfalso. assert (S : scale D a + scale D b == 0) by (rewrite Hn; simpl; ring).
      pose proof (Qplus_lt_le_compat _ _ _ _ Pa (Qlt_le_weak _ _ Pb)) as L.
      rewrite S in L. discriminate L.
Qed.

(**md ## The finer unit *)

(** The measure an integer operation on two measures is inferred at: whichever of the two the
    other converts to exactly. There is none when they are not convertible, or when neither is a
    whole multiple of the other. *)
Definition int_join (D : decls) (a b : measure) : option measure :=
  if convb D a b then
    match int_factor D a b with
    | Some _ => Some b
    | None =>
        match int_factor D b a with
        | Some _ => Some a
        | None => None
        end
    end
  else None.

(**md
**An integer operation on two units is inferred at the finer one.**

When the rule gives a measure, both operands convert to it exactly, and it is the coarsest measure
with that property: any other measure both operands convert to exactly is reached from it by an
exact conversion. An integer in `km` added to one in `m` is therefore in `m`, and no resolution is
lost that the program did not already have.

- [c:] the inferred measure.
*)
Theorem int_join_finest (D : decls) (a b c : measure) :
  int_join D a b = Some c ->
  int_conv D a c /\ int_conv D b c /\
  forall d, int_conv D a d -> int_conv D b d -> int_conv D c d.
Proof.
  unfold int_join. destruct (convb D a b) eqn:C; [| discriminate]. apply convb_iff in C.
  destruct (int_factor D a b) as [n |] eqn:F.
  - intro H. inversion H; subst. apply int_factor_iff in F. split; [| split].
    + split; [exact C | exists n; exact F].
    + exact (proj1 (int_conv_order D c c c)).
    + intros d _ Hd. exact Hd.
  - destruct (int_factor D b a) as [n |] eqn:G; [| discriminate].
    intro H. inversion H; subst. apply int_factor_iff in G. split; [| split].
    + exact (proj1 (int_conv_order D c c c)).
    + split; [apply meq_sym; exact C | exists n; exact G].
    + intros d Hd _. exact Hd.
Qed.

(**md ## Accepted loss of resolution

A position can accept a conversion that is not exact. The value is then rounded down to a whole
number of the target.
*)

(** An integer in one measure, rounded down to a whole number of another.
    - [z:] the integer. *)
Definition truncate (D : decls) (a b : measure) (z : Z) : Z :=
  Qfloor (inject_Z z * cfactor D a b).

(**md
**An accepted loss is less than one unit of the target.**

The rounded value is never above the quantity converted, and the quantity is below the next whole
number of the target. This is the bound a warning can state.
*)
Theorem truncate_bound (D : decls) (a b : measure) (z : Z) :
  inject_Z (truncate D a b z) * scale D b <= inject_Z z * scale D a /\
  inject_Z z * scale D a < inject_Z (truncate D a b z + 1) * scale D b.
Proof.
  unfold truncate. set (x := inject_Z z * cfactor D a b).
  assert (X : inject_Z z * scale D a == x * scale D b).
  { unfold x, cfactor. field. apply scale_nonzero. }
  rewrite X. pose proof (scale_pos D b) as P. split.
  - apply Qmult_le_compat_r; [apply Qfloor_le | apply Qlt_le_weak; exact P].
  - apply Qmult_lt_compat_r; [exact P | apply Qlt_floor].
Qed.

(**md
**Rounding changes nothing where the conversion is exact.**

Where a whole-number factor exists, the rounded value is the integer times that factor.
*)
Theorem truncate_exact (D : decls) (a b : measure) (n z : Z) :
  int_factor D a b = Some n -> truncate D a b z = (z * n)%Z.
Proof.
  unfold int_factor, truncate. intro H. apply qint_iff in H.
  rewrite H, <- inject_Z_mult. apply Qfloor_Z.
Qed.

(**md ## Elaboration of integer expressions

The integer elaboration differs from the rational one in three places.

- Addition of two convertible measures is inferred at the finer one, and the coarser operand is
  scaled by the whole-number factor.
- A position that expects a measure inserts a whole-number scaling when the conversion is exact.
- When it is not exact, the position is an error unless loss is accepted, in which case the value
  is rounded down.
*)

(** A source expression over integers. *)
Inductive iterm : Type :=
| ILit (z : Z) (m : measure)
| IAdd (a b : iterm)
| IMul (a b : iterm)
| IAs (m : measure) (e : iterm).

(** A target expression over integers. `JScale` multiplies by a whole number, and `JTrunc`
    multiplies by a rational and rounds down. *)
Inductive jterm : Type :=
| JLit (z : Z)
| JAdd (a b : jterm)
| JMul (a b : jterm)
| JScale (n : Z) (t : jterm)
| JTrunc (k : Q) (t : jterm).

(** The integer a target expression computes. *)
Fixpoint irun (t : jterm) : Z :=
  match t with
  | JLit z => z
  | JAdd a b => (irun a + irun b)%Z
  | JMul a b => (irun a * irun b)%Z
  | JScale n t => (n * irun t)%Z
  | JTrunc k t => Qfloor (inject_Z (irun t) * k)
  end.

(** The quantity an integer source expression denotes, in base units. *)
Fixpoint imean (D : decls) (e : iterm) : Q :=
  match e with
  | ILit z m => inject_Z z * scale D m
  | IAdd a b => imean D a + imean D b
  | IMul a b => imean D a * imean D b
  | IAs _ e => imean D e
  end.

(** The target expression and measure of an integer source expression.
    - [lossy:] whether positions accept a loss of resolution. *)
Fixpoint ielab (lossy : bool) (D : decls) (e : iterm) : option (jterm * measure) :=
  match e with
  | ILit z m => Some (JLit z, m)
  | IAdd a b =>
      match ielab lossy D a, ielab lossy D b with
      | Some (ta, ma), Some (tb, mb) =>
          if meqb ma mb then Some (JAdd ta tb, ma)
          else if convb D ma mb then
            match int_factor D ma mb with
            | Some n => Some (JAdd (JScale n ta) tb, mb)
            | None =>
                match int_factor D mb ma with
                | Some n => Some (JAdd ta (JScale n tb), ma)
                | None => None
                end
            end
          else None
      | _, _ => None
      end
  | IMul a b =>
      match ielab lossy D a, ielab lossy D b with
      | Some (ta, ma), Some (tb, mb) => Some (JMul ta tb, mmul ma mb)
      | _, _ => None
      end
  | IAs m e =>
      match ielab lossy D e with
      | Some (t, a) =>
          if convb D a m then
            if meqb a m then Some (t, m)
            else
              match int_factor D a m with
              | Some n => Some (JScale n t, m)
              | None => if lossy then Some (JTrunc (cfactor D a m) t, m) else None
              end
          else None
      | None => None
      end
  end.

(**md
**An integer program that checks without accepting loss is exact.**

If an integer expression checks with no position accepting a loss of resolution, the integer its
target computes, read in the measure the checker gave it, is exactly the quantity the source
denotes. This covers the inferred finer unit of an addition: `2 km + 500 m` computes 2500 at `m`.

- [t:] the target expression.
- [m:] the measure the checker gives the expression.
*)
Theorem ielab_exact (D : decls) (e : iterm) (t : jterm) (m : measure) :
  ielab false D e = Some (t, m) -> inject_Z (irun t) * scale D m == imean D e.
Proof.
  revert t m. induction e as [z n | a IHa b IHb | a IHa b IHb | n e IH];
    intros t m H; simpl in H.
  - inversion H; subst. simpl. reflexivity.
  - destruct (ielab false D a) as [[ta ma] |]; [| discriminate].
    destruct (ielab false D b) as [[tb mb] |]; [| discriminate].
    specialize (IHa ta ma eq_refl). specialize (IHb tb mb eq_refl).
    destruct (meqb ma mb) eqn:E.
    { inversion H; subst. simpl. apply meqb_iff in E.
      rewrite inject_Z_plus, <- IHa, <- IHb, (scale_meq D m mb E). ring. }
    destruct (convb D ma mb); [| discriminate].
    destruct (int_factor D ma mb) as [k |] eqn:F.
    { inversion H; subst. simpl. apply int_factor_iff in F.
      rewrite inject_Z_plus, inject_Z_mult, <- IHa, <- IHb, F. ring. }
    destruct (int_factor D mb ma) as [k |] eqn:G; [| discriminate].
    inversion H; subst. simpl. apply int_factor_iff in G.
    rewrite inject_Z_plus, inject_Z_mult, <- IHa, <- IHb, G. ring.
  - destruct (ielab false D a) as [[ta ma] |]; [| discriminate].
    destruct (ielab false D b) as [[tb mb] |]; [| discriminate].
    inversion H; subst. simpl.
    rewrite inject_Z_mult, <- (IHa ta ma eq_refl), <- (IHb tb mb eq_refl), scale_mul. ring.
  - destruct (ielab false D e) as [[t0 a] |]; [| discriminate].
    specialize (IH t0 a eq_refl).
    destruct (convb D a n); [| discriminate].
    destruct (meqb a n) eqn:E.
    { inversion H; subst. apply meqb_iff in E. simpl.
      rewrite <- IH, (scale_meq D a m E). reflexivity. }
    destruct (int_factor D a n) as [k |] eqn:F; [| discriminate].
    inversion H; subst. simpl. apply int_factor_iff in F.
    rewrite inject_Z_mult, <- IH, F. ring.
Qed.

(**md
**Accepting loss changes nothing in a program that has none.**

An integer expression that checks without accepting loss checks to the same target and measure
when loss is accepted. Rounding appears only at the positions that need it.

- [r:] the target expression and measure.
*)
Theorem ielab_lossy_conservative (D : decls) (e : iterm) (r : jterm * measure) :
  ielab false D e = Some r -> ielab true D e = Some r.
Proof.
  revert r. induction e as [z n | a IHa b IHb | a IHa b IHb | n e IH]; intros r H; simpl in *.
  - exact H.
  - destruct (ielab false D a) as [[ta ma] |]; [| discriminate].
    destruct (ielab false D b) as [[tb mb] |]; [| discriminate].
    rewrite (IHa _ eq_refl), (IHb _ eq_refl). exact H.
  - destruct (ielab false D a) as [[ta ma] |]; [| discriminate].
    destruct (ielab false D b) as [[tb mb] |]; [| discriminate].
    rewrite (IHa _ eq_refl), (IHb _ eq_refl). exact H.
  - destruct (ielab false D e) as [[t0 a] |]; [| discriminate].
    rewrite (IH _ eq_refl). destruct (convb D a n); [| discriminate].
    destruct (meqb a n); [exact H |].
    destruct (int_factor D a n); [exact H | discriminate].
Qed.

(**md ## An example *)

Open Scope string_scope.

(** `km`. *)
Definition km : measure := [("km", 1%Z)].

(** `m`. *)
Definition m_ : measure := [("m", 1%Z)].

(** `2<km> + 500<m>` is inferred at `m`, with the `km` operand scaled by 1000. *)
Lemma ex_sum_in_metres :
  ielab false ex (IAdd (ILit 2 km) (ILit 500 m_))
  = Some (JAdd (JScale 1000 (JLit 2)) (JLit 500), m_).
Proof.
  vm_compute. reflexivity.
Qed.

(** `1500<m>` given to a position that expects `km` is an error when loss is not accepted. *)
Lemma ex_metres_as_km_strict : ielab false ex (IAs km (ILit 1500 m_)) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** The same expression checks when loss is accepted, and computes 1. *)
Lemma ex_metres_as_km_lossy :
  exists t, ielab true ex (IAs km (ILit 1500 m_)) = Some (t, km) /\ irun t = 1%Z.
Proof.
  eexists. split; vm_compute; reflexivity.
Qed.
