/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The zero locus of a continuous family of monic polynomials is proper over the parameters

For a family `p : X → K[X]` of **monic** polynomials of one fixed degree whose coefficients vary
continuously, the first projection

    {(x, z) : p x evaluated at z is 0}  ⟶  X

is a proper map: it is closed and its fibres are finite. Finite because a fibre is the root set of
a nonzero polynomial; closed because the roots of a monic polynomial are bounded by its
coefficients, so the zero locus stays inside a fixed ball over a neighbourhood of any parameter,
and there the projection is closed for the reason `isClosedMap_fst_of_compactSpace` is.

Material for `Mathlib/Topology/Algebra/Polynomial.lean`, which is where
`Polynomial.isProperMap_eval` and `Polynomial.isClosedMap_eval` live ; the same statements for the
map `z ↦ q.eval z` of a *single* polynomial. `Polynomial.isProperMap_eval` is a **special case**
of the results below, and that is the argument for the destination: for `q` monic of positive
degree, properness of `z ↦ q.eval z` is `Polynomial.isProperMap_fst_zeroLocus` at `X = K` and the
family `x ↦ q - C x`, transported along the graph homeomorphism `z ↦ (q.eval z, z)` onto the zero
locus of that family ; and dropping monicity costs one further step, composing with
multiplication by `q.leadingCoeff`, a homeomorphism of `K`. (`Polynomial.isClosedMap_eval` is
that together with the constant case, which is `isClosedMap_const` and is not below.) Both
derivations were compiled against this file and neither is kept, because each belongs beside the
theorem it recovers rather than here. Taking `X` to be a point recovers nothing instead: the
projection is then a map into `PUnit`, and no second variable is left to exchange. See
`README.md` on the mirror tree; no statement below mentions anything defined in this repository.

## Why that destination and not the one the proof reads from

The one Mathlib input that file does not already have is `Polynomial.IsRoot.norm_lt_cauchyBound`,
from `Mathlib/Analysis/Polynomial/CauchyBound.lean`. Upstreaming to the *topology* file costs
**3** Mathlib modules on a closure of **1545** ; `Mathlib.Algebra.Field.GeomSum`,
`Mathlib.Algebra.Order.Field.GeomSum` and `Mathlib.Analysis.Polynomial.CauchyBound` itself.
Upstreaming to `Mathlib/Analysis/Polynomial/CauchyBound.lean` instead, which is where the bound
comes from, costs **307** on a closure of **1241**, because that file knows nothing of topology.
Both measured with `python3 scripts/import_cost.py --target …`. **Split by destination, not by
subject**: the subject of the results below is properness, and properness is what the target file
is about.

## The nearest built thing, and what it does not cover

`Other/Oka/Analysis/Complex/CoveringMap.lean` proves exactly this pair ; closed, with finite fibres ;
for `x ↦ xⁿ` on the nonzero elements of a proper normed field (`isClosedMap_npow`,
`finite_fiber_npow`). The family behind those two is `X ^ n - C w` over the punctured base,
parametrised by the *target* point `w`; it is the family `finite_fiber_npow`'s own proof writes
down, and it is **not** a constant one ; a constant family `p ≡ Xⁿ` has zero locus `X × {0}` and
gives nothing. **Both statements do follow from the two halves below.** They are stated in the
disguise where the zero locus has been solved for and presented as the source of a map rather
than as a subset of a product, and undoing that disguise is again a graph homeomorphism,
`x ↦ (xⁿ, x)`; both derivations across it were compiled against this file. The two theorems are
kept where they are because a covering-map file is where they are wanted and their proofs are
self-contained, and nothing below uses them.

What does not transfer is their *proof*. Closedness there comes from `isClosedMap_pow`, which is
the properness of a single polynomial map, and no root bound appears anywhere in that file ;
which is the difference: a family cannot be handled by a statement about one polynomial, and the
bound is what replaces it.

## Why the bound below rather than `Polynomial.cauchyBound`

`Polynomial.cauchyBound q` is
`Finset.sup (Finset.range q.natDegree) (‖q.coeff ·‖₊) / ‖q.leadingCoeff‖₊ + 1`, a `Finset.sup` in
`ℝ≥0` divided by a norm. What the argument needs is a bound that is visibly
*continuous in the family*, and a `Finset.sup` in `ℝ≥0` of continuous `ℝ`-valued functions is one
step of `NNReal` bookkeeping away from being that. `Polynomial.monicRootBound` replaces the
supremum by the sum and the division by nothing ; the leading coefficient is `1` ; so it is a
finite sum of continuous functions and `Polynomial.continuous_monicRootBound` is two lemmas.
It is weaker than Cauchy's bound and it is deduced from it; nothing here needs it to be sharp.

## Main results

- `Polynomial.IsRoot.norm_le_monicRootBound`: **the roots of a monic polynomial are bounded by the
  sum of the norms of its lower coefficients**, plus one.
- `Polynomial.continuous_eval_of_continuous_coeff`: **evaluation of a family of bounded degree is
  jointly continuous** in the parameter and the point.
- `Polynomial.isClosed_fst_image_of_monic`: **the parameters over which a closed set of roots sits
  form a closed set** ; the content of properness, before any packaging.
- `Polynomial.finite_inter_fst_preimage_of_monic`: **a set of roots meets each fibre of the
  projection in a finite set** ; the other half, in the same set-level form.
- `Polynomial.isProperMap_fst_zeroLocus`: **the zero locus of a continuous family of monic
  polynomials of fixed degree is proper over the parameters**, together with its two halves
  `Polynomial.isClosedMap_fst_zeroLocus` and `Polynomial.finite_preimage_fst_zeroLocus`.

## What is not here

* **Nothing complex-analytic.** `K` is any normed field, proper where properness of the ball is
  used; `X` is any topological space. The intended instance is `K = ℂ` and `X` an open subset of
  `ℂ^n`, with `p` the Weierstrass polynomial of a hypersurface, but no holomorphy is used or
  stated and no declaration in this file mentions `ComplexAnalytic`; the only other occurrences of
  the namespace are the citations in the two bullets below.
* **No `ComplexAnalytic.AnalyticSpace.IsFinite`.** Turning the two halves below into finiteness of
  a morphism of analytic spaces needs the analytic structure on the zero locus, which is not the
  subject of this file; it is done in `Other/Oka/AnalyticSpace/MonicProjection.lean`, which is the only
  consumer of anything here and quotes exactly the two set-level statements
  `Polynomial.isClosed_fst_image_of_monic` and `Polynomial.finite_inter_fst_preimage_of_monic`
  across a carrier homeomorphism.
* **No statement about the fibre cardinality.** A fibre is finite, and it has at most `d` points
  because it is the root set of a polynomial of degree `d`; only the finiteness is proved, because
  only the finiteness is what `ComplexAnalytic.AnalyticSpace.IsFinite` asks for. The counting
  statement is `Polynomial.card_roots'` and is not specialised here.
* **No continuity of the roots.** That the root *set* moves continuously with the parameter is a
  different and harder statement; what is proved is that it stays locally bounded, which is all
  properness needs.
-/

@[expose] public section

open Finset Metric NNReal Topology

namespace Polynomial

variable {X K : Type*} [TopologicalSpace X] [NormedField K] {d : ℕ} {p : X → K[X]}

/-! ### A root bound that is continuous in the coefficients -/

/-- **A crude bound on the roots of a monic polynomial of degree `d`**: the sum of the norms of
the coefficients below the leading one, plus one.

Weaker than `Polynomial.cauchyBound`, which uses the supremum in place of the sum, and chosen for
that: a finite sum of norms of continuously varying coefficients is continuous in the parameter
by `Polynomial.continuous_monicRootBound`, with no `NNReal` supremum in the way. -/
noncomputable def monicRootBound (d : ℕ) (q : K[X]) : ℝ := (∑ i ∈ range d, ‖q.coeff i‖) + 1

/-- **The roots of a monic polynomial of degree `d` are bounded by
`Polynomial.monicRootBound d`.**

`Polynomial.IsRoot.norm_lt_cauchyBound` with the supremum bounded by the sum. The leading
coefficient of a monic polynomial is `1`, so the division in `Polynomial.cauchyBound` disappears
rather than having to be estimated. -/
theorem IsRoot.norm_le_monicRootBound {q : K[X]} (hm : q.Monic) (hd : q.natDegree = d) {z : K}
    (hz : q.IsRoot z) : ‖z‖ ≤ monicRootBound d q := by
  have h := hz.norm_lt_cauchyBound hm.ne_zero
  rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hd] at h
  have hsup : (range d).sup (fun i ↦ ‖q.coeff i‖₊) ≤ ∑ i ∈ range d, ‖q.coeff i‖₊ :=
    Finset.sup_le fun i hi ↦
      Finset.single_le_sum (f := fun i ↦ ‖q.coeff i‖₊) (fun _ _ ↦ zero_le) hi
  have h2 : ‖z‖₊ < (∑ i ∈ range d, ‖q.coeff i‖₊) + 1 := h.trans_le (by gcongr)
  have h3 := NNReal.coe_lt_coe.2 h2
  push_cast at h3
  exact h3.le

/-- **The bound varies continuously with the family.** -/
theorem continuous_monicRootBound (hc : ∀ i, Continuous fun x ↦ (p x).coeff i) :
    Continuous fun x ↦ monicRootBound d (p x) := by
  unfold monicRootBound
  exact (continuous_finsetSum _ fun i _ ↦ (hc i).norm).add continuous_const

/-! ### The zero locus of a continuous family -/

/-- **Evaluation of a family of polynomials of bounded degree is jointly continuous** in the
parameter and the point.

The degree bound is what makes this a *finite* sum: `Polynomial.eval_eq_sum_range'` rewrites every
member of the family as the same sum over `Finset.range (d + 1)`, whose terms are continuous
because the coefficients are. Without a uniform bound there is no such sum and the statement is
false ; the coefficient functions of a family of unbounded degree can each be continuous while
the evaluation is not. -/
theorem continuous_eval_of_continuous_coeff (hd : ∀ x, (p x).natDegree ≤ d)
    (hc : ∀ i, Continuous fun x ↦ (p x).coeff i) :
    Continuous fun q : X × K ↦ (p q.1).eval q.2 := by
  have h : ∀ q : X × K, (p q.1).eval q.2 = ∑ i ∈ range (d + 1), (p q.1).coeff i * q.2 ^ i :=
    fun q ↦ eval_eq_sum_range' (Nat.lt_succ_of_le (hd q.1)) q.2
  simp only [h]
  exact continuous_finsetSum _ fun i _ ↦
    ((hc i).comp continuous_fst).mul (continuous_snd.pow i)

/-- **The zero locus of a continuous family of bounded degree is closed** in `X × K`. -/
theorem isClosed_setOf_eval_eq_zero (hd : ∀ x, (p x).natDegree ≤ d)
    (hc : ∀ i, Continuous fun x ↦ (p x).coeff i) :
    IsClosed {q : X × K | (p q.1).eval q.2 = 0} :=
  isClosed_eq (continuous_eval_of_continuous_coeff hd hc) continuous_const

/-! ### Properness over the parameters -/

/-- **A closed set of roots of a continuous family of monic polynomials has closed image in the
parameters.**

This is the whole content of the properness below, stated for a set rather than for a map so that
the subtype version and the `IsProperMap` version are both two lines from it.

The argument is the generalised tube lemma over a ball that works for a whole neighbourhood of the
parameter: `Polynomial.continuous_monicRootBound` gives a neighbourhood `V` of `x₀` on which the
bound stays below a constant `M`, so over `V` every root of the family lies in the closed ball of
radius `M`, which is compact because `K` is proper. `generalized_tube_lemma` applied to `{x₀}` and
that ball separates `s` from a smaller neighbourhood, and intersecting with `V` gives a
neighbourhood of `x₀` missing the image. Monicity enters exactly once, in the bound; the degree
must be constant rather than bounded, since a family whose leading coefficient degenerates has
roots escaping to infinity. -/
theorem isClosed_fst_image_of_monic [ProperSpace K] (hm : ∀ x, (p x).Monic)
    (hd : ∀ x, (p x).natDegree = d) (hc : ∀ i, Continuous fun x ↦ (p x).coeff i)
    {s : Set (X × K)} (hs : IsClosed s) (hsub : ∀ q ∈ s, (p q.1).eval q.2 = 0) :
    IsClosed (Prod.fst '' s) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x₀ hx₀
  set M := monicRootBound d (p x₀) + 1 with hMdef
  have hV : {x | monicRootBound d (p x) < M} ∈ 𝓝 x₀ :=
    (isOpen_lt (continuous_monicRootBound hc) continuous_const).mem_nhds (by simp [hMdef])
  obtain ⟨u, v, hu, _, hxu, hballv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := x₀)) (isCompact_closedBall (0 : K) M)
      hs.isOpen_compl (by
        rintro ⟨x, z⟩ ⟨hx, -⟩
        simp only [Set.mem_singleton_iff] at hx
        subst hx
        exact fun hmem ↦ hx₀ ⟨_, hmem, rfl⟩)
  refine Filter.mem_of_superset (Filter.inter_mem (hu.mem_nhds (hxu rfl)) hV) ?_
  rintro x ⟨hxu', hxV⟩ ⟨⟨x', z⟩, hqs, rfl⟩
  have hz : ‖z‖ ≤ M :=
    ((IsRoot.norm_le_monicRootBound (hm x') (hd x') (hsub _ hqs)).trans_lt hxV).le
  exact huv ⟨hxu', hballv (mem_closedBall_zero_iff.2 hz)⟩ hqs

/-- **The projection of the zero locus to the parameters is a closed map.**

`Polynomial.isClosed_fst_image_of_monic` read on the subtype: a closed subset of the zero locus is
the trace of a closed subset of `X × K`, because the zero locus is itself closed
(`Polynomial.isClosed_setOf_eval_eq_zero`). -/
theorem isClosedMap_fst_zeroLocus [ProperSpace K] (hm : ∀ x, (p x).Monic)
    (hd : ∀ x, (p x).natDegree = d) (hc : ∀ i, Continuous fun x ↦ (p x).coeff i) :
    IsClosedMap fun q : {q : X × K // (p q.1).eval q.2 = 0} ↦ (q : X × K).1 := by
  have hZ : IsClosed {q : X × K | (p q.1).eval q.2 = 0} :=
    isClosed_setOf_eval_eq_zero (fun x ↦ (hd x).le) hc
  intro t ht
  have himg : IsClosed (Subtype.val '' t) := hZ.isClosedEmbedding_subtypeVal.isClosedMap t ht
  have hcomp : (fun q : {q : X × K // (p q.1).eval q.2 = 0} ↦ (q : X × K).1) '' t =
      Prod.fst '' (Subtype.val '' t) := by
    rw [Set.image_image]
  rw [hcomp]
  exact isClosed_fst_image_of_monic hm hd hc himg (by rintro q ⟨a, -, rfl⟩; exact a.2)

omit [TopologicalSpace X] in
/-- **The fibres of the projection are finite**, being the root sets of nonzero polynomials.

Monicity is used only through `Polynomial.Monic.ne_zero`; no degree hypothesis and no topology on
`X` are needed, which is why this half holds for a family that is not continuous at all. -/
theorem finite_preimage_fst_zeroLocus (hm : ∀ x, (p x).Monic) (x₀ : X) :
    Set.Finite ((fun q : {q : X × K // (p q.1).eval q.2 = 0} ↦ (q : X × K).1) ⁻¹' {x₀}) := by
  refine Set.Finite.of_finite_image
    (f := fun q : {q : X × K // (p q.1).eval q.2 = 0} ↦ (q : X × K).2) ?_ ?_
  · refine (finite_setOf_isRoot (hm x₀).ne_zero).subset ?_
    rintro _ ⟨q, hq, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
    simpa [IsRoot.def, hq] using q.2
  · rintro ⟨⟨a, z⟩, ha⟩ hha ⟨⟨b, w⟩, hb⟩ hhb h
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hha hhb
    simp_all

omit [TopologicalSpace X] in
/-- **A set of roots of a family of monic polynomials meets each fibre of the projection in a
finite set.**

The companion of `Polynomial.isClosed_fst_image_of_monic`: both are about an arbitrary set of
roots rather than about the whole zero locus, so that a consumer holding a subset ; the image of
a closed embedding, say ; can quote them without first cutting it out.
`Polynomial.finite_preimage_fst_zeroLocus` is the case where the set is the whole zero locus,
read on the subtype.

Like that theorem this needs no degree hypothesis and no topology on `X`, monicity entering only
through `Polynomial.Monic.ne_zero`; the fibre injects into the root set of the single polynomial
`p x₀`, by `Prod.snd`, which is injective on a fibre because the first coordinate is fixed. -/
theorem finite_inter_fst_preimage_of_monic (hm : ∀ x, (p x).Monic) (x₀ : X) {s : Set (X × K)}
    (hsub : ∀ q ∈ s, (p q.1).eval q.2 = 0) : (s ∩ Prod.fst ⁻¹' {x₀}).Finite := by
  refine Set.Finite.of_finite_image (f := Prod.snd) ?_ ?_
  · refine (finite_setOf_isRoot (hm x₀).ne_zero).subset ?_
    rintro _ ⟨q, ⟨hq, hq'⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq'
    simpa [IsRoot.def, ← hq'] using hsub q hq
  · rintro ⟨a, z⟩ ⟨-, ha⟩ ⟨b, w⟩ ⟨-, hb⟩ h
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    simp_all

/-- **The zero locus of a continuous family of monic polynomials of one fixed degree is proper
over the parameters.**

The two halves are `Polynomial.isClosedMap_fst_zeroLocus` and
`Polynomial.finite_preimage_fst_zeroLocus`, assembled by
`isProperMap_iff_isClosedMap_and_compact_fibers`; a finite set is compact, which is the only step
that is not one of the two. -/
theorem isProperMap_fst_zeroLocus [ProperSpace K] (hm : ∀ x, (p x).Monic)
    (hd : ∀ x, (p x).natDegree = d) (hc : ∀ i, Continuous fun x ↦ (p x).coeff i) :
    IsProperMap fun q : {q : X × K // (p q.1).eval q.2 = 0} ↦ (q : X × K).1 :=
  isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨continuous_fst.comp continuous_subtype_val, isClosedMap_fst_zeroLocus hm hd hc,
      fun x ↦ (finite_preimage_fst_zeroLocus hm x).isCompact⟩

end Polynomial

end
