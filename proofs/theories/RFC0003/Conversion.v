From Stdlib Require Import List ZArith QArith Qpower String Bool Lia.
Import ListNotations.
From Clef Require Import RFC0003.Measures.

(**md # Conversion between units

A unit is declared with its size relative to other units:

```fsharp
[<Measure>] type m
[<Measure>] type s
[<Measure>] type km = 1000 m
[<Measure>] type h  = 3600 s
```

From the declarations every measure gets two readings. Its *dimension* is the measure written in
base units, and its *scale* is the number that turns a value in the measure into a value in those
base units. `km/h` has dimension `m/s` and scale `1000/3600`.

Two measures are convertible when their dimensions are equal. The factor between them is the
quotient of their scales. No table of pairwise formulas is declared, so there is nothing to keep
consistent: this module proves the factor between any two convertible measures is determined.
*)

Open Scope Q_scope.

(**md ## Declarations *)

(** The unit declarations of a program.
    `basedim` gives a unit's expression in base units: `m` for `km`, and `m` for `m` itself.
    `factor` gives its size in those base units: `1000` for `km`, and `1` for `m`.
    `factor_pos` is the rule that a declared size is positive. *)
Record decls : Type := Decls {
  basedim : uname -> measure;
  factor : uname -> Q;
  factor_pos : forall u, 0 < factor u
}.

(** The dimension of a measure: the measure rewritten in base units.
    - [D:] the unit declarations.
    - [m:] the measure. *)
Fixpoint dim (D : decls) (m : measure) : measure :=
  match m with
  | [] => []
  | (u, z) :: r => mmul (mpow z (basedim D u)) (dim D r)
  end.

(** The scale of a measure: the size of one of it in base units. *)
Definition scale (D : decls) (m : measure) : Q := evalq (factor D) m.

(** Two measures are convertible when they have the same dimension. *)
Definition conv (D : decls) (a b : measure) : Prop := meq (dim D a) (dim D b).

(** Convertibility as a computed test. *)
Definition convb (D : decls) (a b : measure) : bool := meqb (dim D a) (dim D b).

(** The conversion factor: multiply a value in the first measure by it to get the value in the
    second.
    - [a:] the measure converted from.
    - [b:] the measure converted to. *)
Definition cfactor (D : decls) (a b : measure) : Q := scale D a / scale D b.

(**md ## The two readings are well defined *)

(** The exponent of a base unit in a dimension is a weighted sum through the measure. *)
Lemma expo_dim (D : decls) (m : measure) (v : uname) :
  expo (dim D m) v = lin (fun u => expo (basedim D u) v) m.
Proof.
  induction m as [| [u z] m IH]; simpl; [reflexivity |].
  rewrite expo_mul, expo_pow, IH. reflexivity.
Qed.

(** Equal measures have equal dimensions. *)
Lemma dim_meq (D : decls) (a b : measure) : meq a b -> meq (dim D a) (dim D b).
Proof.
  intros H v. rewrite !expo_dim. apply lin_meq. exact H.
Qed.

(** The dimension of a product is the product of the dimensions. *)
Lemma dim_mul (D : decls) (a b : measure) : meq (dim D (mmul a b)) (mmul (dim D a) (dim D b)).
Proof.
  intro v. rewrite expo_mul, !expo_dim, lin_mul. reflexivity.
Qed.

(** The dimension of a power is the power of the dimension. *)
Lemma dim_pow (D : decls) (k : Z) (a : measure) : meq (dim D (mpow k a)) (mpow k (dim D a)).
Proof.
  intro v. rewrite expo_pow, !expo_dim, lin_pow. reflexivity.
Qed.

(** The scale of a measure is positive. *)
Lemma scale_pos (D : decls) (m : measure) : 0 < scale D m.
Proof.
  apply evalq_pos. apply factor_pos.
Qed.

(** The scale of a measure is not zero. *)
Lemma scale_nonzero (D : decls) (m : measure) : ~ scale D m == 0.
Proof.
  apply Qpos_nonzero. apply scale_pos.
Qed.

(** Equal measures have equal scales. *)
Lemma scale_meq (D : decls) (a b : measure) : meq a b -> scale D a == scale D b.
Proof.
  apply evalq_meq. apply factor_pos.
Qed.

(** The scale of a product is the product of the scales. *)
Lemma scale_mul (D : decls) (a b : measure) : scale D (mmul a b) == scale D a * scale D b.
Proof.
  apply evalq_mul.
Qed.

(** The scale of a power is the power of the scale. *)
Lemma scale_pow (D : decls) (k : Z) (a : measure) : scale D (mpow k a) == scale D a ^ k.
Proof.
  apply evalq_pow.
Qed.

(** The scale of a quotient is the quotient of the scales. *)
Lemma scale_div (D : decls) (a b : measure) : scale D (mdiv a b) == scale D a / scale D b.
Proof.
  unfold mdiv, minv. rewrite scale_mul, scale_pow. reflexivity.
Qed.

(**md
**Dimension and scale do not depend on how a measure is written.**

Two annotations that name the same measure have the same dimension and the same scale. The
conversion the compiler inserts therefore depends on the measure, not on the order or grouping of
the units in the source.
*)
Theorem readings_well_defined (D : decls) (a b : measure) :
  meq a b -> meq (dim D a) (dim D b) /\ scale D a == scale D b.
Proof.
  intro H. split; [apply dim_meq | apply scale_meq]; exact H.
Qed.

(**md ## Convertibility *)

(**md
**Whether two measures are convertible is decidable.**

The test compares the two dimensions, which are measures, with the computed equality of
[Measures](Clef.RFC0003.Measures.html).
*)
Theorem convb_iff (D : decls) (a b : measure) : convb D a b = true <-> conv D a b.
Proof.
  apply meqb_iff.
Qed.

(**md
**Convertibility is an equivalence that contains equality.**

Every measure is convertible to itself, the relation is symmetric and transitive, and equal
measures are convertible. The measures of a program therefore fall into classes, one per
dimension, and a conversion never leaves its class.
*)
Theorem conv_equivalence (D : decls) (a b c : measure) :
  conv D a a /\
  (conv D a b -> conv D b a) /\
  (conv D a b -> conv D b c -> conv D a c) /\
  (meq a b -> conv D a b).
Proof.
  unfold conv. split; [| split; [| split]].
  - apply meq_refl.
  - apply meq_sym.
  - apply meq_trans.
  - apply dim_meq.
Qed.

(**md ## Coherence *)

(**md
**The conversion factor does not depend on the path.**

Converting a measure to itself multiplies by one. Converting through an intermediate measure
multiplies by the same number as converting directly, and converting there and back multiplies by
one. Whatever chain of conversions the compiler builds between two measures, the product of its
factors is the factor of the direct conversion.
*)
Theorem coherence (D : decls) (a b c : measure) :
  cfactor D a a == 1 /\
  cfactor D a b * cfactor D b c == cfactor D a c /\
  cfactor D a b * cfactor D b a == 1.
Proof.
  unfold cfactor.
  pose proof (scale_nonzero D a). pose proof (scale_nonzero D b). pose proof (scale_nonzero D c).
  split; [| split]; field; auto.
Qed.

(**md
**Equal measures convert with factor one.**

Where the measure of a value and the measure expected of it are equal, the factor is one, so no
scaling is needed. A program with no unit mismatch is unchanged.
*)
Theorem cfactor_equal (D : decls) (a b : measure) : meq a b -> cfactor D a b == 1.
Proof.
  intro H. unfold cfactor. rewrite (scale_meq D a b H). field. apply scale_nonzero.
Qed.

(**md
**Compound measures need no declarations of their own.**

Convertibility and the factor both follow the structure of a measure. If `a` converts to `a'` and
`b` to `b'`, then the product `a b` converts to `a' b'` and its factor is the product of the two
factors; a power converts with the power of the factor. So `km/h` to `m/s` follows from the
declarations of `km` and `h`.

- [k:] the power.
*)
Theorem compound (D : decls) (a a' b b' : measure) (k : Z) :
  conv D a a' -> conv D b b' ->
  conv D (mmul a b) (mmul a' b') /\
  cfactor D (mmul a b) (mmul a' b') == cfactor D a a' * cfactor D b b' /\
  conv D (mpow k a) (mpow k a') /\
  cfactor D (mpow k a) (mpow k a') == cfactor D a a' ^ k.
Proof.
  unfold conv, cfactor. intros Ha Hb.
  pose proof (scale_nonzero D a'). pose proof (scale_nonzero D b').
  split; [| split; [| split]].
  - eapply meq_trans; [apply dim_mul |]. eapply meq_trans; [| apply meq_sym; apply dim_mul].
    apply mmul_meq; assumption.
  - rewrite !scale_mul. field. auto.
  - eapply meq_trans; [apply dim_pow |]. eapply meq_trans; [| apply meq_sym; apply dim_pow].
    apply mpow_meq. exact Ha.
  - rewrite !scale_pow. symmetry. apply Qdiv_power.
Qed.

(**md ## Dimensions that are named and related

A dimension can be given a name, and one dimension can be defined from others:

```fsharp
[<Dimension>] type distance = m
[<Dimension>] type time     = s
[<Dimension>] type speed    = distance / time

let f (v: speed<m/s>) = ...
```

A parameter of type `speed<m/s>` accepts a value in any measure of that dimension and holds it in
`m/s`. In the model a dimension is the class of measures convertible to a representative, so
`distance` is the class of `m`. The theorem below is what makes `speed = distance / time` a
definition and not a second declaration to keep in step.
*)

(**md
**A dimension defined as a quotient accepts every quotient of its parts.**

If `a` is a measure of the first dimension and `b` of the second, then `a/b` is a measure of the
quotient dimension, and its factor is the quotient of the two factors. Any distance over any time
is a speed, with no declaration naming the pair.

- [d:] the representative of the first dimension.
- [t:] the representative of the second dimension.
*)
Theorem quotient_dimension (D : decls) (a b d t : measure) :
  conv D a d -> conv D b t ->
  conv D (mdiv a b) (mdiv d t) /\
  (cfactor D (mdiv a b) (mdiv d t) == cfactor D a d / cfactor D b t).
Proof.
  intros Ha Hb. unfold mdiv, minv.
  destruct (compound D b t b t (-1)%Z Hb Hb) as [_ [_ [Cp Fp]]].
  destruct (compound D a d (mpow (-1) b) (mpow (-1) t) 0%Z Ha Cp) as [Cm [Fm _]].
  split; [exact Cm |]. rewrite Fm, Fp. reflexivity.
Qed.

(**md ## The choice of base unit *)

(** The scale under declarations whose sizes are given relative to rescaled base units. *)
Lemma scale_rescaled (D D' : decls) (k : uname -> Q) (m : measure) :
  (forall u, factor D' u == factor D u * evalq k (basedim D u)) ->
  scale D' m == scale D m * evalq k (dim D m).
Proof.
  intro R. unfold scale. induction m as [| [u z] m IH]; simpl; [ring |].
  rewrite IH, R, Qmult_power, evalq_mul, evalq_pow. ring.
Qed.

(**md
**The choice of base unit does not change any conversion.**

Suppose a second set of declarations gives every size relative to different base units, each old
base unit being some positive multiple of a new one. `Length` declared from `km` instead of `m` is
an example. The factor between two convertible measures is the same under both sets.

- [D:] the first declarations, which also decide what is convertible.
- [D':] the second declarations.
- [k:] the size of each old base unit in the new base units.
*)
Theorem base_independent (D D' : decls) (k : uname -> Q) (a b : measure) :
  (forall u, 0 < k u) ->
  (forall u, factor D' u == factor D u * evalq k (basedim D u)) ->
  conv D a b ->
  cfactor D' a b == cfactor D a b.
Proof.
  intros P R C. unfold cfactor. rewrite !(scale_rescaled D D' k) by exact R.
  rewrite (evalq_meq k (dim D a) (dim D b) P C).
  pose proof (scale_nonzero D b). pose proof (Qpos_nonzero _ (evalq_pos k (dim D b) P)).
  field. auto.
Qed.

(**md ## An example *)

Open Scope string_scope.

(** The size of each unit in the example: `km = 1000 m`, `h = 3600 s`, `mi = 1609.344 m`. *)
Definition ex_factor (u : uname) : Q :=
  if ueqb u "km" then 1000
  else if ueqb u "h" then 3600
  else if ueqb u "mi" then 1609344 # 1000
  else 1.

(** The base expression of each unit in the example. *)
Definition ex_basedim (u : uname) : measure :=
  if ueqb u "km" then [("m", 1%Z)]
  else if ueqb u "h" then [("s", 1%Z)]
  else if ueqb u "mi" then [("m", 1%Z)]
  else [(u, 1%Z)].

(** Every size in the example is positive. *)
Lemma ex_factor_pos (u : uname) : 0 < ex_factor u.
Proof.
  unfold ex_factor. repeat destruct (ueqb u _); reflexivity.
Qed.

(** The example declarations. *)
Definition ex : decls := Decls ex_basedim ex_factor ex_factor_pos.

(** `km/h`. *)
Definition kmh : measure := [("km", 1%Z); ("h", (-1)%Z)].

(** `m/s`. *)
Definition ms : measure := [("m", 1%Z); ("s", (-1)%Z)].

(** `km/h` converts to `m/s`, and the factor is 5/18. *)
Lemma ex_kmh_to_ms : convb ex kmh ms = true /\ Qred (cfactor ex kmh ms) = 5 # 18.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** `km` does not convert to `s`. *)
Lemma ex_km_not_s : convb ex [("km", 1%Z)] [("s", 1%Z)] = false.
Proof.
  vm_compute. reflexivity.
Qed.
