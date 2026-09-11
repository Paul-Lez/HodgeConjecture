/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Analysis.PolynomialFactorGrowth
public import Other.Analysis.Complex.FiniteSingularityPolynomial
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Factors selected on the simple-root cover

This file studies a monic polynomial whose coefficients are polynomials in one complex
parameter.  Over the locus where every root is simple, a subset of the root cover canonically
selects a monic factor in each fiber.
-/

@[expose] public section

open scoped Polynomial Topology
open Filter
open Set

namespace Polynomial

noncomputable section

/-- Specialization of a one-parameter polynomial family. -/
def familySpecialization (p : Polynomial (Polynomial ℂ)) (z : ℂ) : Polynomial ℂ :=
  p.map (Polynomial.evalRingHom z)

/-- The equation of the polynomial family in parameter-root coordinates. -/
def familyEquation (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) : ℂ :=
  (familySpecialization p zw.1).eval zw.2

theorem analyticAt_familyEquation (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) :
    AnalyticAt ℂ (familyEquation p) zw := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show familyEquation (p + q) = fun u ↦ familyEquation p u + familyEquation q u by
        funext u
        simp [familyEquation, familySpecialization]]
      exact hp.add hq
  | monomial k a =>
      rw [show familyEquation (Polynomial.monomial k a) =
          fun u : ℂ × ℂ ↦ a.eval u.1 * u.2 ^ k by
        funext u
        simp [familyEquation, familySpecialization]]
      exact ((AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) a) zw.1 (Set.mem_univ _)).comp (ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.fst ℂ ℂ ℂ) zw) |>.mul
          ((ContinuousLinearMap.analyticAt
            (ContinuousLinearMap.snd ℂ ℂ ℂ) zw).pow k)

theorem fderiv_familyEquation_comp_inr (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) :
    fderiv ℂ (familyEquation p) zw ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((familySpecialization p zw.1).derivative.eval zw.2) := by
  have hins : HasFDerivAt (fun t : ℂ ↦ (zw.1, t))
      (ContinuousLinearMap.inr ℂ ℂ ℂ) zw.2 :=
    (hasFDerivAt_const zw.1 zw.2).prodMk (hasFDerivAt_id zw.2)
  have hchain := ((analyticAt_familyEquation p zw).differentiableAt).hasFDerivAt.comp zw.2 hins
  have hchain' : HasFDerivAt (fun t : ℂ ↦ (familySpecialization p zw.1).eval t)
      (fderiv ℂ (familyEquation p) zw ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) zw.2 := by
    simpa [Function.comp_def, familyEquation] using hchain
  have hpoly := (familySpecialization p zw.1).hasFDerivAt zw.2
  simpa using hchain'.unique hpoly

theorem hasStrictFDerivAt_familyEquation (p : Polynomial (Polynomial ℂ)) (zw : ℂ × ℂ) :
    HasStrictFDerivAt (familyEquation p) (fderiv ℂ (familyEquation p) zw) zw :=
  (analyticAt_familyEquation p zw).hasStrictFDerivAt

/-- The parameter locus on which all roots of a polynomial family are simple. -/
abbrev SimpleRootBase (p : Polynomial (Polynomial ℂ)) :=
  {z : ℂ // ∀ w : ℂ, (familySpecialization p z).eval w = 0 →
    (familySpecialization p z).derivative.eval w ≠ 0}

/-- The simple-root cover of a one-parameter polynomial family. -/
abbrev SimpleRootCover (p : Polynomial (Polynomial ℂ)) :=
  {zw : SimpleRootBase p × ℂ // (familySpecialization p zw.1.1).eval zw.2 = 0}

/-- Projection of the simple-root cover to its parameter. -/
def SimpleRootCover.proj {p : Polynomial (Polynomial ℂ)} : SimpleRootCover p → SimpleRootBase p :=
  fun zw ↦ zw.1.1

lemma simpleRootCover_rootDirection_isInvertible {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) :
    (fderiv ℂ (familyEquation p) (zw.1.1.1, zw.1.2) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  rw [fderiv_familyEquation_comp_inr]
  let d := (familySpecialization p zw.1.1.1).derivative.eval zw.1.2
  have hd : d ≠ 0 := zw.1.1.2 zw.1.2 zw.2
  change (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d⁻¹)
  · ext
    simp [hd]
  · ext
    simp [hd]

/-- The implicit local root branch through a point of the simple-root cover. -/
noncomputable def localRootBranch {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) : ℂ → ℂ :=
  let hs := hasStrictFDerivAt_familyEquation p (zw.1.1.1, zw.1.2)
  hs.implicitFunctionOfProdDomain (simpleRootCover_rootDirection_isInvertible zw)

theorem hasStrictFDerivAt_localRootBranch {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) :
    HasStrictFDerivAt (localRootBranch zw)
      (-(fderiv ℂ (familyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inr ℂ ℂ ℂ).inverse ∘L
        (fderiv ℂ (familyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inl ℂ ℂ ℂ)) zw.1.1.1 := by
  simpa [localRootBranch] using
    (hasStrictFDerivAt_familyEquation p (zw.1.1.1, zw.1.2)).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (simpleRootCover_rootDirection_isInvertible zw)

theorem localRootBranch_apply_base {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) : localRootBranch zw zw.1.1.1 = zw.1.2 := by
  let hs := hasStrictFDerivAt_familyEquation p (zw.1.1.1, zw.1.2)
  have h := (hs.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (simpleRootCover_rootDirection_isInvertible zw)).self_of_nhds
  apply h.mp
  rfl

theorem differentiableAt_localRootBranch {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) : DifferentiableAt ℂ (localRootBranch zw) zw.1.1.1 :=
  (hasStrictFDerivAt_localRootBranch zw).differentiableAt

/-- Near its center, the implicit branch consists of roots of the specialized family. -/
theorem eventually_familyEquation_localRootBranch {p : Polynomial (Polynomial ℂ)}
    (zw : SimpleRootCover p) :
    ∀ᶠ z in 𝓝 zw.1.1.1, familyEquation p (z, localRootBranch zw z) = 0 := by
  let hs := hasStrictFDerivAt_familyEquation p (zw.1.1.1, zw.1.2)
  have h := hs.eventually_apply_implicitFunctionOfProdDomain
    (simpleRootCover_rootDirection_isInvertible zw)
  have hzero : familyEquation p (zw.1.1.1, zw.1.2) = 0 := zw.2
  simpa [localRootBranch, hzero] using h

/-- A fiber over the simple-root locus has the expected number of distinct roots. -/
theorem roots_card_nodup_of_mem_simpleRootBase {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) :
    (familySpecialization p z.1).roots.card = p.natDegree ∧
      (familySpecialization p z.1).roots.Nodup := by
  let q := familySpecialization p z.1
  have hq : q.Monic := by
    exact hp.map (Polynomial.evalRingHom z.1)
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hcard : q.roots.card = q.natDegree :=
    hsplit.natDegree_eq_card_roots.symm
  have hdegree : q.natDegree = p.natDegree := by
    exact hp.natDegree_map (Polynomial.evalRingHom z.1)
  refine ⟨hcard.trans hdegree, ?_⟩
  rw [nodup_roots_iff_of_splits hq.ne_zero hsplit]
  rw [Separable, ← gcd_isUnit_iff, isUnit_iff_degree_eq_zero]
  by_contra hnot
  obtain ⟨w, hw⟩ := Splits.exists_eval_eq_zero
    (Splits.of_dvd hsplit hq.ne_zero (gcd_dvd_left q q.derivative)) hnot
  exact z.2 w
    (eval_eq_zero_of_dvd_of_eval_eq_zero (gcd_dvd_left q q.derivative) hw)
    (eval_eq_zero_of_dvd_of_eval_eq_zero (gcd_dvd_right q q.derivative) hw)

/-- An explicit enumeration of the roots of a simple fiber. -/
noncomputable def simpleRootEnumeration {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) : Fin p.natDegree → ℂ :=
  let r := (familySpecialization p z.1).roots
  let hcard : r.toFinset.card = p.natDegree :=
    (Multiset.toFinset_card_of_nodup
      (roots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (roots_card_nodup_of_mem_simpleRootBase hp z).1
  fun i ↦ ((r.toFinset.equivFinOfCardEq hcard).symm i : ℂ)

theorem simpleRootEnumeration_isRoot {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (i : Fin p.natDegree) :
    (familySpecialization p z.1).eval (simpleRootEnumeration hp z i) = 0 := by
  apply (mem_roots (hp.map (Polynomial.evalRingHom z.1)).ne_zero).mp
  change simpleRootEnumeration hp z i ∈
    (familySpecialization p z.1).roots
  let e := ((familySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (roots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (roots_card_nodup_of_mem_simpleRootBase hp z).1)).symm
  refine Multiset.mem_toFinset.mp ?_
  change (((familySpecialization p z.1).roots.toFinset.equivFinOfCardEq
    ((Multiset.toFinset_card_of_nodup
      (roots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (roots_card_nodup_of_mem_simpleRootBase hp z).1)).symm i : ℂ) ∈
    (familySpecialization p z.1).roots.toFinset
  exact (e i).property

theorem simpleRootEnumeration_injective {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) :
    Function.Injective (simpleRootEnumeration hp z) := by
  intro i j hij
  have hsub : ((familySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (roots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (roots_card_nodup_of_mem_simpleRootBase hp z).1)).symm i =
      ((familySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (roots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (roots_card_nodup_of_mem_simpleRootBase hp z).1)).symm j := by
    exact Subtype.ext (by simpa [simpleRootEnumeration] using hij)
  exact (Equiv.injective _ hsub)

theorem exists_simpleRootEnumeration {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (w : ℂ)
    (hw : (familySpecialization p z.1).eval w = 0) :
    ∃ i : Fin p.natDegree, simpleRootEnumeration hp z i = w := by
  have hmem : w ∈ (familySpecialization p z.1).roots :=
    (mem_roots (hp.map (Polynomial.evalRingHom z.1)).ne_zero).mpr hw
  let e := ((familySpecialization p z.1).roots.toFinset.equivFinOfCardEq
    ((Multiset.toFinset_card_of_nodup
      (roots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (roots_card_nodup_of_mem_simpleRootBase hp z).1)).symm
  have hwfin : w ∈ (familySpecialization p z.1).roots.toFinset := by
    simpa using hmem
  refine ⟨e.symm ⟨w, hwfin⟩, ?_⟩
  simp [simpleRootEnumeration, e]

/-- The point of the root cover attached to an enumerated root of a simple fiber. -/
noncomputable def simpleRootCoverPoint {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (i : Fin p.natDegree) : SimpleRootCover p :=
  ⟨(z, simpleRootEnumeration hp z i), simpleRootEnumeration_isRoot hp z i⟩

/-- One neighborhood of the base point supports all the finitely many local root branches. -/
theorem eventually_all_familyEquation_localRootBranch {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ i : Fin p.natDegree,
      familyEquation p (z', localRootBranch (simpleRootCoverPoint hp z i) z') = 0 := by
  exact eventually_all.2 fun i ↦
    eventually_familyEquation_localRootBranch (simpleRootCoverPoint hp z i)

/-- Near the center, the finitely many root branches remain pairwise distinct. -/
theorem eventually_injective_localRootBranches {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, Function.Injective
      (fun i : Fin p.natDegree ↦ localRootBranch (simpleRootCoverPoint hp z i) z') := by
  have hpair : ∀ i j : Fin p.natDegree, i ≠ j →
      ∀ᶠ z' in 𝓝 z.1,
        localRootBranch (simpleRootCoverPoint hp z i) z' ≠
          localRootBranch (simpleRootCoverPoint hp z j) z' := by
    intro i j hij
    have hne : localRootBranch (simpleRootCoverPoint hp z i) z.1 -
        localRootBranch (simpleRootCoverPoint hp z j) z.1 ≠ 0 := by
      have hi : localRootBranch (simpleRootCoverPoint hp z i) z.1 =
          simpleRootEnumeration hp z i := by
        change localRootBranch (simpleRootCoverPoint hp z i)
          (simpleRootCoverPoint hp z i).1.1.1 = _
        exact localRootBranch_apply_base _
      have hj : localRootBranch (simpleRootCoverPoint hp z j) z.1 =
          simpleRootEnumeration hp z j := by
        change localRootBranch (simpleRootCoverPoint hp z j)
          (simpleRootCoverPoint hp z j).1.1.1 = _
        exact localRootBranch_apply_base _
      rw [hi, hj]
      exact sub_ne_zero.mpr (fun h ↦ hij (simpleRootEnumeration_injective hp z h))
    have hcont :=
      (differentiableAt_localRootBranch (simpleRootCoverPoint hp z i)).continuousAt.sub
        (differentiableAt_localRootBranch (simpleRootCoverPoint hp z j)).continuousAt
    filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hne)] with z' hz
    exact sub_ne_zero.mp hz
  filter_upwards [eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    eventually_all.2 fun hij : i ≠ j ↦ hpair i j hij] with z' hz
  intro i j heq
  by_contra hij
  exact hz i j hij heq

/-- On a common neighborhood, the local branches exhaust every root of every fiber. -/
theorem eventually_exists_localRootBranch_eq_of_familyEquation_eq_zero
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic) (z : SimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ w : ℂ, familyEquation p (z', w) = 0 →
      ∃ i : Fin p.natDegree, localRootBranch (simpleRootCoverPoint hp z i) z' = w := by
  filter_upwards [eventually_all_familyEquation_localRootBranch hp z,
    eventually_injective_localRootBranches hp z] with z' hroot hinj
  intro w hw
  let q := familySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ localRootBranch (simpleRootCoverPoint hp z i) z'
  let B : Finset ℂ := Finset.univ.image f
  have hq : q.Monic := hp.map (Polynomial.evalRingHom z')
  have hdegree : q.natDegree = p.natDegree := hp.natDegree_map (Polynomial.evalRingHom z')
  have hBcard : B.card = p.natDegree := by
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hBroot : ∀ a ∈ B, q.eval a = 0 := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hroot i
  have hroots : q.roots = B.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero hBroot
    simpa [hdegree] using hBcard.ge
    exact hq.ne_zero
  have hmem : w ∈ B := by
    have hwroot : w ∈ q.roots := (mem_roots hq.ne_zero).mpr hw
    have : w ∈ B.val := by rwa [hroots] at hwroot
    simpa using this
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi⟩

/-- The multiset of roots in a fiber which belong to a specified subset of the root cover. -/
def selectedRoots {p : Polynomial (Polynomial ℂ)}
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) : Multiset ℂ := by
  classical
  exact (familySpecialization p z.1).roots.filter fun w ↦
    ∃ h : (familySpecialization p z.1).eval w = 0,
      (⟨(z, w), h⟩ : SimpleRootCover p) ∈ S

/-- The monic fiber factor selected by a subset of the simple-root cover. -/
def selectedFactor {p : Polynomial (Polynomial ℂ)} (_hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) : Polynomial ℂ :=
  ((selectedRoots S z).map fun w ↦ X - C w).prod

theorem selectedFactor_monic {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    (selectedFactor hp S z).Monic := by
  exact monic_multisetProd_X_sub_C (selectedRoots S z)

theorem selectedFactor_dvd {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    selectedFactor hp S z ∣ familySpecialization p z.1 := by
  classical
  rw [selectedFactor, selectedRoots]
  exact (Multiset.prod_dvd_prod_of_le
    (Multiset.map_le_map (Multiset.filter_le _ _))).trans
      (familySpecialization p z.1).prod_multiset_X_sub_C_dvd

theorem natDegree_selectedFactor {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    (selectedFactor hp S z).natDegree =
      (selectedRoots S z).card := by
  simp [selectedFactor]

/-- The factor formed from a fixed finite set of the local root branches at `z`. -/
noncomputable def localBranchFactor {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (I : Finset (Fin p.natDegree)) :
    ℂ → Polynomial ℂ :=
  fun z' ↦ (I.1.map fun i ↦ X - C (localRootBranch (simpleRootCoverPoint hp z i) z')).prod

theorem localBranchFactor_monic {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (I : Finset (Fin p.natDegree)) (z' : ℂ) :
    (localBranchFactor hp z I z').Monic := by
  unfold localBranchFactor
  simpa only [Multiset.map_map, Function.comp_apply] using
    monic_multisetProd_X_sub_C (I.1.map fun i : Fin p.natDegree ↦
      localRootBranch (simpleRootCoverPoint hp z i) z')

theorem natDegree_localBranchFactor {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (I : Finset (Fin p.natDegree)) (z' : ℂ) :
    (localBranchFactor hp z I z').natDegree = I.card := by
  simp [localBranchFactor]

/-- On the common branch neighborhood, a factor from any fixed branch subset divides the fiber. -/
theorem eventually_localBranchFactor_dvd {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (I : Finset (Fin p.natDegree)) :
    ∀ᶠ z' in 𝓝 z.1, localBranchFactor hp z I z' ∣ familySpecialization p z' := by
  filter_upwards [eventually_all_familyEquation_localRootBranch hp z,
    eventually_injective_localRootBranches hp z] with z' hroot hinj
  let q := familySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ localRootBranch (simpleRootCoverPoint hp z i) z'
  have hsubset : I.1.map f ⊆ q.roots := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hw
    exact (mem_roots (hp.map (Polynomial.evalRingHom z')).ne_zero).mpr (hroot i)
  have hnodup : (I.1.map f).Nodup :=
    (Multiset.nodup_map_iff_of_injective hinj).2 I.nodup
  have hle : I.1.map f ≤ q.roots := (Multiset.le_iff_subset hnodup).2 hsubset
  change (I.1.map fun i ↦ X - C (localRootBranch (simpleRootCoverPoint hp z i) z')).prod ∣ q
  simpa only [Multiset.map_map, Function.comp_apply, f] using
    (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)).trans
      q.prod_multiset_X_sub_C_dvd

/-- The simple-root base contains a neighborhood of each of its points. -/
theorem eventually_mem_simpleRootBase {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ w : ℂ, (familySpecialization p z').eval w = 0 →
      (familySpecialization p z').derivative.eval w ≠ 0 := by
  filter_upwards [eventually_all_familyEquation_localRootBranch hp z,
    eventually_injective_localRootBranches hp z,
    eventually_exists_localRootBranch_eq_of_familyEquation_eq_zero hp z] with z' hroot hinj hexhaust
  let q := familySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ localRootBranch (simpleRootCoverPoint hp z i) z'
  let B : Finset ℂ := Finset.univ.image f
  have hq : q.Monic := hp.map (Polynomial.evalRingHom z')
  have hdegree : q.natDegree = p.natDegree := hp.natDegree_map (Polynomial.evalRingHom z')
  have hBcard : B.card = p.natDegree := by
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hBroot : ∀ a ∈ B, q.eval a = 0 := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hroot i
  have hroots : q.roots = B.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero hBroot
    simpa [hdegree] using hBcard.ge
    exact hq.ne_zero
  intro w hw
  have hnodup : q.roots.Nodup := by rw [hroots]; exact B.nodup
  have hseparable : q.Separable :=
    (nodup_roots_iff_of_splits hq.ne_zero (IsAlgClosed.splits q)).mp hnodup
  intro hderiv
  have hdiv : X - C w ∣ gcd q q.derivative :=
    dvd_gcd (dvd_iff_isRoot.mpr hw) (dvd_iff_isRoot.mpr hderiv)
  exact not_isUnit_X_sub_C w
    (isUnit_of_dvd_unit hdiv ((gcd_isUnit_iff q q.derivative).mpr hseparable))

/-- Membership of a local root branch in a clopen part of the root cover is locally constant. -/
theorem eventually_mem_clopen_localRootBranch_iff {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (S : Set (SimpleRootCover p)) (hSopen : IsOpen S)
    (hSclosed : IsClosed S) (z : SimpleRootBase p) (i : Fin p.natDegree) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (familySpecialization p z').eval w = 0 →
        (familySpecialization p z').derivative.eval w ≠ 0)
      (hroot : familyEquation p
        (z', localRootBranch (simpleRootCoverPoint hp z i) z') = 0),
      (⟨(⟨z', hbase⟩, localRootBranch (simpleRootCoverPoint hp z i) z'), hroot⟩ :
          SimpleRootCover p) ∈ S ↔ simpleRootCoverPoint hp z i ∈ S := by
  let U : Set ℂ := {z' | (∀ w : ℂ, (familySpecialization p z').eval w = 0 →
      (familySpecialization p z').derivative.eval w ≠ 0) ∧
    familyEquation p (z', localRootBranch (simpleRootCoverPoint hp z i) z') = 0}
  have hU : U ∈ 𝓝 z.1 := inter_mem (eventually_mem_simpleRootBase hp z)
    (eventually_familyEquation_localRootBranch (simpleRootCoverPoint hp z i))
  have hzU : z.1 ∈ U := by
    refine ⟨z.2, ?_⟩
    have hbranch : localRootBranch (simpleRootCoverPoint hp z i) z.1 =
        simpleRootEnumeration hp z i := by
      simpa [simpleRootCoverPoint] using
        localRootBranch_apply_base (simpleRootCoverPoint hp z i)
    rw [familyEquation, hbranch]
    exact simpleRootEnumeration_isRoot hp z i
  let g : U → SimpleRootCover p := fun x ↦
    ⟨(⟨x.1, x.2.1⟩, localRootBranch (simpleRootCoverPoint hp z i) x.1), x.2.2⟩
  have hg : ContinuousAt g ⟨z.1, hzU⟩ := by
    apply ContinuousAt.codRestrict
    apply ContinuousAt.prodMk
    · exact continuousAt_subtype_val.codRestrict fun x ↦ x.2.1
    · have hbranch :=
        (differentiableAt_localRootBranch (simpleRootCoverPoint hp z i)).continuousAt
      have hbranch' : ContinuousAt (localRootBranch (simpleRootCoverPoint hp z i)) z.1 := by
        simpa [simpleRootCoverPoint] using hbranch
      have hval : ContinuousAt ((↑) : U → ℂ) ⟨z.1, hzU⟩ := continuousAt_subtype_val
      change ContinuousAt
        (localRootBranch (simpleRootCoverPoint hp z i) ∘ ((↑) : U → ℂ)) ⟨z.1, hzU⟩
      exact hbranch'.comp_of_eq hval rfl
  have hg_center : g ⟨z.1, hzU⟩ = simpleRootCoverPoint hp z i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change localRootBranch (simpleRootCoverPoint hp z i) z.1 = simpleRootEnumeration hp z i
      exact localRootBranch_apply_base _
  have hmap : Filter.map ((↑) : U → ℂ) (𝓝 ⟨z.1, hzU⟩) = 𝓝 z.1 :=
    map_nhds_subtype_coe_eq_nhds hzU hU
  by_cases hi : simpleRootCoverPoint hp z i ∈ S
  · have hevent : ∀ᶠ x in 𝓝 (⟨z.1, hzU⟩ : U), g x ∈ S :=
      hg (hSopen.mem_nhds (hg_center.symm ▸ hi))
    have hevent' : ∀ᶠ z' in 𝓝 z.1, ∀ hz' : z' ∈ U, g ⟨z', hz'⟩ ∈ S := by
      rw [← hmap, eventually_map]
      filter_upwards [hevent] with x hx
      intro hx'
      convert hx using 1
    filter_upwards [hU, hevent'] with z' hz' hmem hbase hroot
    exact ⟨fun _ ↦ hi, fun _ ↦ by simpa only [g, Subtype.ext_iff] using hmem hz'⟩
  · have hevent : ∀ᶠ x in 𝓝 (⟨z.1, hzU⟩ : U), g x ∈ Sᶜ :=
      hg (hSclosed.isOpen_compl.mem_nhds (by simpa [hg_center] using hi))
    have hevent' : ∀ᶠ z' in 𝓝 z.1, ∀ hz' : z' ∈ U, g ⟨z', hz'⟩ ∈ Sᶜ := by
      rw [← hmap, eventually_map]
      filter_upwards [hevent] with x hx
      intro hx'
      convert hx using 1
    filter_upwards [hU, hevent'] with z' hz' hmem hbase hroot
    exact ⟨fun h ↦ ((hmem hz') h).elim, fun h ↦ (hi h).elim⟩

/-- The branch indices selected by `S` in the fiber over `z`. -/
noncomputable def selectedBranchIndices {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) : Finset (Fin p.natDegree) :=
  by
    classical
    exact Finset.univ.filter fun i ↦ simpleRootCoverPoint hp z i ∈ S

/-- Near a fiber, a clopen selection consists of the same fixed set of local branches. -/
theorem eventually_selectedRoots_eq_map_localRootBranches {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (S : Set (SimpleRootCover p)) (hSopen : IsOpen S)
    (hSclosed : IsClosed S) (z : SimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ hbase : ∀ w : ℂ, (familySpecialization p z').eval w = 0 →
        (familySpecialization p z').derivative.eval w ≠ 0,
      selectedRoots S ⟨z', hbase⟩ =
        (selectedBranchIndices hp S z).1.map fun i ↦
          localRootBranch (simpleRootCoverPoint hp z i) z' := by
  classical
  have hselection : ∀ᶠ z' in 𝓝 z.1, ∀ i : Fin p.natDegree,
      ∀ (hbase : ∀ w : ℂ, (familySpecialization p z').eval w = 0 →
          (familySpecialization p z').derivative.eval w ≠ 0)
        (hroot : familyEquation p
          (z', localRootBranch (simpleRootCoverPoint hp z i) z') = 0),
        (⟨(⟨z', hbase⟩, localRootBranch (simpleRootCoverPoint hp z i) z'), hroot⟩ :
            SimpleRootCover p) ∈ S ↔ simpleRootCoverPoint hp z i ∈ S :=
    eventually_all.2 fun i ↦ eventually_mem_clopen_localRootBranch_iff hp S hSopen hSclosed z i
  filter_upwards [eventually_mem_simpleRootBase hp z,
    eventually_all_familyEquation_localRootBranch hp z,
    eventually_injective_localRootBranches hp z,
    eventually_exists_localRootBranch_eq_of_familyEquation_eq_zero hp z,
    hselection] with z' hbase hroot hinj hexhaust hselect
  intro hbase'
  let q := familySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ localRootBranch (simpleRootCoverPoint hp z i) z'
  rw [selectedRoots]
  apply (Multiset.Nodup.ext (s := _) (t := _)
    ((roots_card_nodup_of_mem_simpleRootBase hp ⟨z', hbase'⟩).2.filter _)
    ((Multiset.nodup_map_iff_of_injective hinj).2 (selectedBranchIndices hp S z).nodup)).2
  intro w
  constructor
  · intro hw
    rw [Multiset.mem_filter] at hw
    obtain ⟨hwroot, hmem⟩ := hw
    have hweval : q.eval w = 0 :=
      (mem_roots (hp.map (Polynomial.evalRingHom z')).ne_zero).mp hwroot
    obtain ⟨i, hi⟩ := hexhaust w hweval
    rw [Multiset.mem_map]
    refine ⟨i, ?_, hi⟩
    obtain ⟨hwproof, hwS⟩ := hmem
    have hbranchS :
        (⟨(⟨z', hbase'⟩, localRootBranch (simpleRootCoverPoint hp z i) z'), hroot i⟩ :
          SimpleRootCover p) ∈ S := by
      convert hwS using 1
      all_goals simp [hi]
    change i ∈ selectedBranchIndices hp S z
    simpa [selectedBranchIndices] using (hselect i hbase' (hroot i)).mp hbranchS
  · intro hw
    rw [Multiset.mem_map] at hw
    obtain ⟨i, hiI, rfl⟩ := hw
    rw [Multiset.mem_filter]
    refine ⟨(mem_roots (hp.map (Polynomial.evalRingHom z')).ne_zero).mpr (hroot i), ?_⟩
    refine ⟨hroot i, ?_⟩
    apply (hselect i hbase' (hroot i)).mpr
    simpa [selectedBranchIndices] using hiI

/-- Near a fiber, the selected factor is the product of a fixed set of local branches. -/
theorem eventually_selectedFactor_eq_localBranchFactor {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (S : Set (SimpleRootCover p)) (hSopen : IsOpen S)
    (hSclosed : IsClosed S) (z : SimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ hbase : ∀ w : ℂ, (familySpecialization p z').eval w = 0 →
        (familySpecialization p z').derivative.eval w ≠ 0,
      selectedFactor hp S ⟨z', hbase⟩ =
        localBranchFactor hp z (selectedBranchIndices hp S z) z' := by
  filter_upwards [eventually_selectedRoots_eq_map_localRootBranches hp S hSopen hSclosed z]
    with z' hz' hbase
  rw [selectedFactor, localBranchFactor, hz' hbase, Multiset.map_map]
  rfl

/-- The degree of the factor selected by a clopen set is locally constant. -/
theorem eventually_natDegree_selectedFactor_eq_card_selectedBranchIndices
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic) (S : Set (SimpleRootCover p))
    (hSopen : IsOpen S) (hSclosed : IsClosed S) (z : SimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ hbase : ∀ w : ℂ, (familySpecialization p z').eval w = 0 →
        (familySpecialization p z').derivative.eval w ≠ 0,
      (selectedFactor hp S ⟨z', hbase⟩).natDegree = (selectedBranchIndices hp S z).card := by
  filter_upwards [eventually_selectedFactor_eq_localBranchFactor hp S hSopen hSclosed z]
    with z' hz' hbase
  rw [hz' hbase, natDegree_localBranchFactor]

private theorem differentiableAt_coeff_X_sub_C_localRootBranch {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (i : Fin p.natDegree) (k : ℕ) :
    DifferentiableAt ℂ
      (fun z' ↦ (X - C (localRootBranch (simpleRootCoverPoint hp z i) z')).coeff k) z.1 := by
  rcases k with _ | k
  · simpa [simpleRootCoverPoint] using
      (differentiableAt_localRootBranch (simpleRootCoverPoint hp z i)).neg
  rcases k with _ | k
  · simp
  · simp

/-- Every coefficient of a fixed product of local root branches is holomorphic at its center. -/
theorem differentiableAt_coeff_localBranchFactor {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (z : SimpleRootBase p) (I : Finset (Fin p.natDegree)) (k : ℕ) :
    DifferentiableAt ℂ (fun z' ↦ (localBranchFactor hp z I z').coeff k) z.1 := by
  induction I using Finset.induction_on generalizing k with
  | empty => simp [localBranchFactor]
  | @insert i I hi hI =>
      have hfactor : localBranchFactor hp z (insert i I) = fun z' ↦
          (X - C (localRootBranch (simpleRootCoverPoint hp z i) z')) *
            localBranchFactor hp z I z' := by
        funext z'
        simp [localBranchFactor, hi]
      rw [hfactor]
      simp_rw [coeff_mul]
      apply DifferentiableAt.fun_sum
      intro ij hij
      exact (differentiableAt_coeff_X_sub_C_localRootBranch hp z i ij.1).mul (hI ij.2)

/-- Parameters at which the specialized family has a multiple root. -/
def nonsimpleParameters (p : Polynomial (Polynomial ℂ)) : Set ℂ :=
  {z | ¬ ∀ w : ℂ, (familySpecialization p z).eval w = 0 →
    (familySpecialization p z).derivative.eval w ≠ 0}

/-- Extend one coefficient of a clopen-selected factor by zero at nonsimple parameters. -/
noncomputable def selectedFactorCoeffTotal {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (k : ℕ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∉ nonsimpleParameters p then
    (selectedFactor hp S ⟨z, not_not.mp hz⟩).coeff k else 0

theorem selectedFactorCoeffTotal_eq {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (k : ℕ) (z : ℂ) (hz : z ∉ nonsimpleParameters p) :
    selectedFactorCoeffTotal hp S k z = (selectedFactor hp S ⟨z, not_not.mp hz⟩).coeff k := by
  simp [selectedFactorCoeffTotal, hz]

/-- Away from the nonsimple fibers, coefficients selected by a clopen set are holomorphic. -/
theorem differentiableOn_selectedFactorCoeffTotal {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (S : Set (SimpleRootCover p)) (hSopen : IsOpen S)
    (hSclosed : IsClosed S) (k : ℕ) :
    DifferentiableOn ℂ (selectedFactorCoeffTotal hp S k) (nonsimpleParameters p)ᶜ := by
  intro z hz
  have hzsimple : z ∉ nonsimpleParameters p := hz
  let zbase : SimpleRootBase p := ⟨z, not_not.mp hzsimple⟩
  let I := selectedBranchIndices hp S zbase
  have heq : ∀ᶠ z' in 𝓝 z,
      selectedFactorCoeffTotal hp S k z' = (localBranchFactor hp zbase I z').coeff k := by
    filter_upwards [eventually_mem_simpleRootBase hp zbase,
      eventually_selectedFactor_eq_localBranchFactor hp S hSopen hSclosed zbase]
      with z' hbase hfactor
    have hz' : z' ∉ nonsimpleParameters p := by
      simpa [nonsimpleParameters] using hbase
    rw [selectedFactorCoeffTotal_eq hp S k z' hz']
    simpa only [I, Subtype.ext_iff] using congrArg (fun q : Polynomial ℂ ↦ q.coeff k) (hfactor hbase)
  exact ((differentiableAt_coeff_localBranchFactor hp zbase I k).congr_of_eventuallyEq
    heq).differentiableWithinAt

/-- The coefficients of a clopen-selected factor satisfy one uniform polynomial-growth bound. -/
theorem exists_selectedFactorCoeffTotal_growth {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (S : Set (SimpleRootCover p)) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k z, z ∉ nonsimpleParameters p →
      ‖selectedFactorCoeffTotal hp S k z‖ ≤ C * (1 + ‖z‖) ^ N := by
  obtain ⟨C, N, hC, hbound⟩ := exists_monic_factor_coeff_growth p hp
  refine ⟨C, N, hC, fun k z hz ↦ ?_⟩
  rw [selectedFactorCoeffTotal_eq hp S k z hz]
  exact hbound z _ (selectedFactor_monic hp S ⟨z, not_not.mp hz⟩)
    (selectedFactor_dvd hp S ⟨z, not_not.mp hz⟩) k

/-- If only finitely many fibers have multiple roots, every selected coefficient algebraizes. -/
theorem exists_polynomial_selectedFactorCoeff {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (S : Set (SimpleRootCover p)) (hSopen : IsOpen S)
    (hSclosed : IsClosed S) (hfinite : (nonsimpleParameters p).Finite) (k : ℕ) :
    ∃ a : Polynomial ℂ, ∀ z (hz : z ∉ nonsimpleParameters p),
      a.eval z = (selectedFactor hp S ⟨z, not_not.mp hz⟩).coeff k := by
  obtain ⟨C, N, hC, hbound⟩ := exists_selectedFactorCoeffTotal_growth hp S
  obtain ⟨a, -, ha⟩ := Complex.exists_polynomial_of_polynomial_growth_off_finite hfinite
    (differentiableOn_selectedFactorCoeffTotal hp S hSopen hSclosed k) hC N
    (fun z hz ↦ hbound k z hz)
  exact ⟨a, fun z hz ↦ (ha z hz).trans (selectedFactorCoeffTotal_eq hp S k z hz)⟩

/-- With finitely many nonsimple fibers, a clopen-selected fiber factor is the specialization
of a polynomial family. -/
theorem exists_polynomialFamily_selectedFactor {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) (S : Set (SimpleRootCover p)) (hSopen : IsOpen S)
    (hSclosed : IsClosed S) (hfinite : (nonsimpleParameters p).Finite) :
    ∃ q : Polynomial (Polynomial ℂ),
      q.natDegree ≤ p.natDegree ∧ ∀ z (hz : z ∉ nonsimpleParameters p),
        q.map (Polynomial.evalRingHom z) = selectedFactor hp S ⟨z, not_not.mp hz⟩ := by
  classical
  choose a ha using fun k ↦
    exists_polynomial_selectedFactorCoeff hp S hSopen hSclosed hfinite k
  let q : Polynomial (Polynomial ℂ) :=
    ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (a k)
  have hqdegree : q.natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have hqcoeff : q.coeff k =
        ∑ x ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial x (a x)).coeff k := by
      simp [q]
    rw [hqcoeff]
    apply Finset.sum_eq_zero
    intro x hx
    apply coeff_monomial_of_ne
    exact ne_of_gt (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hx)) hk)
  refine ⟨q, hqdegree, fun z hz ↦ ?_⟩
  ext k
  rw [coeff_map]
  have hqcoeff : q.coeff k =
      ∑ x ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial x (a x)).coeff k := by
    simp [q]
  rw [hqcoeff, map_sum]
  by_cases hk : k ≤ p.natDegree
  · rw [Finset.sum_eq_single k]
    · rw [coeff_monomial_same]
      simpa only [coe_evalRingHom] using ha k z hz
    · intro x hx hxk
      rw [coeff_monomial_of_ne _ hxk.symm]
      simp
    · exact fun h ↦ (h (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))).elim
  · have hdegree : (selectedFactor hp S ⟨z, not_not.mp hz⟩).natDegree ≤ p.natDegree :=
      (natDegree_le_of_dvd (selectedFactor_dvd hp S ⟨z, not_not.mp hz⟩)
        (hp.map (Polynomial.evalRingHom z)).ne_zero).trans_eq
          (hp.natDegree_map (Polynomial.evalRingHom z))
    have hcoeff : (selectedFactor hp S ⟨z, not_not.mp hz⟩).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (lt_of_not_ge hk))
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro x hx
    have hxk : x ≠ k := fun h ↦ hk (h ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hx))
    rw [coeff_monomial_of_ne _ hxk.symm]
    simp

/-- The algebraized selected family divides the original family after every simple
specialization. -/
theorem exists_polynomialFamily_selectedFactor_dvd_on_simple
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic) (S : Set (SimpleRootCover p))
    (hSopen : IsOpen S) (hSclosed : IsClosed S) (hfinite : (nonsimpleParameters p).Finite) :
    ∃ q : Polynomial (Polynomial ℂ), ∀ z (_hz : z ∉ nonsimpleParameters p),
      q.map (Polynomial.evalRingHom z) ∣ p.map (Polynomial.evalRingHom z) := by
  obtain ⟨q, -, hq⟩ := exists_polynomialFamily_selectedFactor hp S hSopen hSclosed hfinite
  exact ⟨q, fun z hz ↦ (hq z hz).symm ▸ selectedFactor_dvd hp S ⟨z, not_not.mp hz⟩⟩

/-- If the selected fiber degree is constant, its algebraization can be chosen monic. -/
theorem exists_monic_polynomialFamily_selectedFactor_of_constant_degree
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic) (S : Set (SimpleRootCover p))
    (hSopen : IsOpen S) (hSclosed : IsClosed S) (hfinite : (nonsimpleParameters p).Finite)
    (d : ℕ) (hdegree : ∀ z (hz : z ∉ nonsimpleParameters p),
      (selectedFactor hp S ⟨z, not_not.mp hz⟩).natDegree = d) :
    ∃ q : Polynomial (Polynomial ℂ), q.Monic ∧ ∀ z (hz : z ∉ nonsimpleParameters p),
      q.map (Polynomial.evalRingHom z) = selectedFactor hp S ⟨z, not_not.mp hz⟩ := by
  obtain ⟨q, hqdegree, hq⟩ :=
    exists_polynomialFamily_selectedFactor hp S hSopen hSclosed hfinite
  have hdle : d ≤ p.natDegree := by
    obtain ⟨z, hz⟩ := hfinite.infinite_compl.nonempty
    rw [← hdegree z hz]
    exact (natDegree_le_of_dvd (selectedFactor_dvd hp S ⟨z, not_not.mp hz⟩)
      (hp.map (Polynomial.evalRingHom z)).ne_zero).trans_eq
        (hp.natDegree_map (Polynomial.evalRingHom z))
  have habove : ∀ k, d < k → q.coeff k = 0 := by
    intro k hk
    apply eq_zero_of_infinite_isRoot
    apply hfinite.infinite_compl.mono
    intro z hz
    have hcoeff := congrArg (fun r : Polynomial ℂ ↦ r.coeff k) (hq z hz)
    rw [coeff_map] at hcoeff
    have hzero : (selectedFactor hp S ⟨z, not_not.mp hz⟩).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa [hdegree z hz] using hk)
    simpa [IsRoot, hzero] using hcoeff
  have hqle : q.natDegree ≤ d := natDegree_le_iff_coeff_eq_zero.mpr habove
  have hcoeffd : q.coeff d = 1 := by
    have heq : q.coeff d = (1 : Polynomial ℂ) := by
      apply (q.coeff d).eq_of_infinite_eval_eq 1
      apply hfinite.infinite_compl.mono
      intro z hz
      have hcoeff := congrArg (fun r : Polynomial ℂ ↦ r.coeff d) (hq z hz)
      rw [coeff_map] at hcoeff
      have hmonic := (selectedFactor_monic hp S ⟨z, not_not.mp hz⟩).coeff_natDegree
      rw [hdegree z hz] at hmonic
      simpa [hmonic] using hcoeff
    exact heq
  have hqnatDegree : q.natDegree = d :=
    natDegree_eq_of_le_of_coeff_ne_zero hqle (hcoeffd.symm ▸ one_ne_zero)
  refine ⟨q, ?_, hq⟩
  rw [Monic, leadingCoeff, hqnatDegree, hcoeffd]

/-- A resultant whose zeros contain every parameter with a multiple root. -/
noncomputable def ramificationPolynomial (p : Polynomial (Polynomial ℂ)) : Polynomial ℂ :=
  resultant p p.derivative p.natDegree (p.natDegree - 1)

theorem eval_ramificationPolynomial {p : Polynomial (Polynomial ℂ)} (z : ℂ) :
    (ramificationPolynomial p).eval z =
      resultant (familySpecialization p z) (familySpecialization p z).derivative
        p.natDegree (p.natDegree - 1) := by
  change (Polynomial.evalRingHom z) (resultant p p.derivative p.natDegree
    (p.natDegree - 1)) = _
  calc
    _ = resultant (p.map (Polynomial.evalRingHom z))
        (p.derivative.map (Polynomial.evalRingHom z)) p.natDegree (p.natDegree - 1) :=
      (resultant_map_map p p.derivative p.natDegree (p.natDegree - 1)
        (Polynomial.evalRingHom z)).symm
    _ = _ := by
      simp only [familySpecialization]
      rw [derivative_map]

/-- Every nonsimple parameter is a zero of the resultant polynomial. -/
theorem nonsimpleParameters_subset_ramificationPolynomial_zero {p : Polynomial (Polynomial ℂ)}
    (hp : p.Monic) :
    nonsimpleParameters p ⊆ {z | (ramificationPolynomial p).eval z = 0} := by
  intro z hz
  rw [nonsimpleParameters] at hz
  push Not at hz
  obtain ⟨w, hw, hwd⟩ := hz
  let q := familySpecialization p z
  have hq : q.Monic := hp.map (Polynomial.evalRingHom z)
  have hncp : ¬IsCoprime q q.derivative := by
    intro hc
    obtain ⟨a, b, hab⟩ := hc
    have heval := congrArg (Polynomial.eval w) hab
    have hwq : q.eval w = 0 := by simpa [q] using hw
    have hwdq : q.derivative.eval w = 0 := by simpa [q] using hwd
    rw [eval_add, eval_mul, eval_mul, hwq, hwdq] at heval
    simp at heval
  have hres : resultant q q.derivative = 0 :=
    resultant_eq_zero_iff.mpr ⟨Or.inl hq.ne_zero, hncp⟩
  have hdegree : q.natDegree = p.natDegree := by
    simpa [q, familySpecialization] using hp.natDegree_map (Polynomial.evalRingHom z)
  rw [hdegree, natDegree_derivative, hdegree] at hres
  change (ramificationPolynomial p).eval z = 0
  rw [eval_ramificationPolynomial]
  exact hres

/-- Generic squarefreeness makes the set of nonsimple parameters finite. -/
theorem finite_nonsimpleParameters_of_ramificationPolynomial_ne_zero
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic) (hram : ramificationPolynomial p ≠ 0) :
    (nonsimpleParameters p).Finite := by
  apply (ramificationPolynomial p).rootSet_finite ℂ |>.subset
  intro z hz
  apply (mem_rootSet_of_ne hram).mpr
  simpa using nonsimpleParameters_subset_ramificationPolynomial_zero hp hz

/-- Coprimality with the derivative over the coefficient ring is one sufficient generic
squarefreeness hypothesis. -/
theorem ramificationPolynomial_ne_zero_of_isCoprime {p : Polynomial (Polynomial ℂ)}
    (hcoprime : IsCoprime p p.derivative) : ramificationPolynomial p ≠ 0 := by
  simpa [ramificationPolynomial, natDegree_derivative] using
    resultant_ne_zero p p.derivative hcoprime

/-- Generic squarefreeness over the rational function field makes the resultant polynomial
nonzero. -/
theorem ramificationPolynomial_ne_zero_of_isCoprime_fractionRing
    {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (hcoprime : IsCoprime
      (p.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))))
      (p.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).derivative) :
    ramificationPolynomial p ≠ 0 := by
  let K := FractionRing (Polynomial ℂ)
  let φ : Polynomial ℂ →+* K := algebraMap (Polynomial ℂ) K
  let pK : Polynomial K := p.map φ
  have hdegree : pK.natDegree = p.natDegree := by
    exact hp.natDegree_map φ
  have hres : resultant pK pK.derivative p.natDegree (p.natDegree - 1) ≠ 0 := by
    simpa only [hdegree, natDegree_derivative] using resultant_ne_zero pK pK.derivative hcoprime
  intro hzero
  apply hres
  have hmap : φ (ramificationPolynomial p) =
      resultant pK pK.derivative p.natDegree (p.natDegree - 1) := by
    rw [ramificationPolynomial]
    calc
      _ = resultant (p.map φ) (p.derivative.map φ) p.natDegree (p.natDegree - 1) :=
        (resultant_map_map p p.derivative p.natDegree (p.natDegree - 1) φ).symm
      _ = _ := by
        change resultant pK (p.derivative.map φ) p.natDegree (p.natDegree - 1) = _
        rw [derivative_map]
  rw [hzero, map_zero] at hmap
  exact hmap.symm

end

end Polynomial
