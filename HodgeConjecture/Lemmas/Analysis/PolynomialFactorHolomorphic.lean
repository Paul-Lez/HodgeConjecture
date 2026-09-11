/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Analysis.PolynomialFactorGrowth
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Algebra.Polynomial.Splits

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
def SimpleRootBase (p : Polynomial (Polynomial ℂ)) :=
  {z : ℂ // ∀ w : ℂ, (familySpecialization p z).eval w = 0 →
    (familySpecialization p z).derivative.eval w ≠ 0}

/-- The simple-root cover of a one-parameter polynomial family. -/
def SimpleRootCover (p : Polynomial (Polynomial ℂ)) :=
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

end

end Polynomial
