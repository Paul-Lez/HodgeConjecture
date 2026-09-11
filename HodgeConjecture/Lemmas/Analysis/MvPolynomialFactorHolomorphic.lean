/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Analysis.PolynomialFactorHolomorphic

/-!
# Factors in multivariable polynomial families

The local analytic theory for a polynomial whose coefficients depend polynomially on a
finite-dimensional complex parameter space.
-/

@[expose] public section

open scoped Polynomial Topology
open Filter Set

namespace Polynomial

noncomputable section

/-- Specialization of a multivariable polynomial family. -/
def mvFamilySpecialization {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (z : Fin n → ℂ) : Polynomial ℂ :=
  p.map (MvPolynomial.eval z)

/-- The equation of a multivariable polynomial family in parameter-root coordinates. -/
def mvFamilyEquation {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (zw : (Fin n → ℂ) × ℂ) : ℂ :=
  (mvFamilySpecialization p zw.1).eval zw.2

theorem analyticAt_mvFamilyEquation {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (zw : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (mvFamilyEquation p) zw := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show mvFamilyEquation (p + q) =
          fun u ↦ mvFamilyEquation p u + mvFamilyEquation q u by
        funext u
        simp [mvFamilyEquation, mvFamilySpecialization]]
      exact hp.add hq
  | monomial k a =>
      rw [show mvFamilyEquation (Polynomial.monomial k a) =
          fun u : (Fin n → ℂ) × ℂ ↦ MvPolynomial.eval u.1 a * u.2 ^ k by
        funext u
        simp [mvFamilyEquation, mvFamilySpecialization]]
      have ha : AnalyticAt ℂ (fun z : Fin n → ℂ ↦ MvPolynomial.eval z a) zw.1 :=
        AnalyticOnNhd.eval_mvPolynomial a zw.1 (Set.mem_univ _)
      exact (ha.comp (ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ) zw)).mul
          ((ContinuousLinearMap.analyticAt
            (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) zw).pow k)

theorem fderiv_mvFamilyEquation_comp_inr {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (zw : (Fin n → ℂ) × ℂ) :
    fderiv ℂ (mvFamilyEquation p) zw ∘L ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((mvFamilySpecialization p zw.1).derivative.eval zw.2) := by
  have hins : HasFDerivAt (fun t : ℂ ↦ (zw.1, t))
      (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) zw.2 :=
    (hasFDerivAt_const zw.1 zw.2).prodMk (hasFDerivAt_id zw.2)
  have hchain := ((analyticAt_mvFamilyEquation p zw).differentiableAt).hasFDerivAt.comp zw.2 hins
  have hchain' : HasFDerivAt (fun t : ℂ ↦ (mvFamilySpecialization p zw.1).eval t)
      (fderiv ℂ (mvFamilyEquation p) zw ∘L
        ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ) zw.2 := by
    simpa [Function.comp_def, mvFamilyEquation] using hchain
  exact hchain'.unique ((mvFamilySpecialization p zw.1).hasFDerivAt zw.2)

theorem hasStrictFDerivAt_mvFamilyEquation {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) ℂ)) (zw : (Fin n → ℂ) × ℂ) :
    HasStrictFDerivAt (mvFamilyEquation p) (fderiv ℂ (mvFamilyEquation p) zw) zw :=
  (analyticAt_mvFamilyEquation p zw).hasStrictFDerivAt

/-- The parameter locus on which all roots are simple. -/
abbrev MvSimpleRootBase {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :=
  {z : Fin n → ℂ // ∀ w : ℂ, (mvFamilySpecialization p z).eval w = 0 →
    (mvFamilySpecialization p z).derivative.eval w ≠ 0}

/-- The root cover above the simple-root locus. -/
abbrev MvSimpleRootCover {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :=
  {zw : MvSimpleRootBase p × ℂ // (mvFamilySpecialization p zw.1.1).eval zw.2 = 0}

def MvSimpleRootCover.proj {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)} :
    MvSimpleRootCover p → MvSimpleRootBase p := fun zw ↦ zw.1.1

lemma mvSimpleRootCover_rootDirection_isInvertible {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    (fderiv ℂ (mvFamilyEquation p) (zw.1.1.1, zw.1.2) ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible := by
  rw [fderiv_mvFamilyEquation_comp_inr]
  let d := (mvFamilySpecialization p zw.1.1.1).derivative.eval zw.1.2
  have hd : d ≠ 0 := zw.1.1.2 zw.1.2 zw.2
  change (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d⁻¹)
  · ext
    simp [hd]
  · ext
    simp [hd]

/-- The implicit local root branch through a point of the multivariable root cover. -/
noncomputable def mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    (Fin n → ℂ) → ℂ :=
  (hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)).implicitFunctionOfProdDomain
    (mvSimpleRootCover_rootDirection_isInvertible zw)

theorem hasStrictFDerivAt_mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    HasStrictFDerivAt (mvLocalRootBranch zw)
      (-(fderiv ℂ (mvFamilyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).inverse ∘L
        (fderiv ℂ (mvFamilyEquation p) (zw.1.1.1, zw.1.2) ∘L
          ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ)) zw.1.1.1 := by
  simpa [mvLocalRootBranch] using
    (hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (mvSimpleRootCover_rootDirection_isInvertible zw)

theorem mvLocalRootBranch_apply_base {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    mvLocalRootBranch zw zw.1.1.1 = zw.1.2 := by
  let hs := hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)
  have h := (hs.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (mvSimpleRootCover_rootDirection_isInvertible zw)).self_of_nhds
  apply h.mp
  rfl

theorem differentiableAt_mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    DifferentiableAt ℂ (mvLocalRootBranch zw) zw.1.1.1 :=
  (hasStrictFDerivAt_mvLocalRootBranch zw).differentiableAt

theorem eventually_mvFamilyEquation_mvLocalRootBranch {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (zw : MvSimpleRootCover p) :
    ∀ᶠ z in 𝓝 zw.1.1.1, mvFamilyEquation p (z, mvLocalRootBranch zw z) = 0 := by
  let hs := hasStrictFDerivAt_mvFamilyEquation p (zw.1.1.1, zw.1.2)
  have h := hs.eventually_apply_implicitFunctionOfProdDomain
    (mvSimpleRootCover_rootDirection_isInvertible zw)
  have hzero : mvFamilyEquation p (zw.1.1.1, zw.1.2) = 0 := zw.2
  simpa [mvLocalRootBranch, hzero] using h


/-- A fiber over the simple-root locus has the expected number of distinct roots. -/
theorem mvRoots_card_nodup_of_mem_simpleRootBase {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    (mvFamilySpecialization p z.1).roots.card = p.natDegree ∧
      (mvFamilySpecialization p z.1).roots.Nodup := by
  let q := mvFamilySpecialization p z.1
  have hq : q.Monic := by
    exact hp.map (MvPolynomial.eval z.1)
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hcard : q.roots.card = q.natDegree :=
    hsplit.natDegree_eq_card_roots.symm
  have hdegree : q.natDegree = p.natDegree := by
    exact hp.natDegree_map (MvPolynomial.eval z.1)
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
noncomputable def mvSimpleRootEnumeration {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) : Fin p.natDegree → ℂ :=
  let r := (mvFamilySpecialization p z.1).roots
  let hcard : r.toFinset.card = p.natDegree :=
    (Multiset.toFinset_card_of_nodup
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1
  fun i ↦ ((r.toFinset.equivFinOfCardEq hcard).symm i : ℂ)

theorem mvSimpleRootEnumeration_isRoot {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) (i : Fin p.natDegree) :
    (mvFamilySpecialization p z.1).eval (mvSimpleRootEnumeration hp z i) = 0 := by
  apply (mem_roots (hp.map (MvPolynomial.eval z.1)).ne_zero).mp
  change mvSimpleRootEnumeration hp z i ∈
    (mvFamilySpecialization p z.1).roots
  let e := ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm
  refine Multiset.mem_toFinset.mp ?_
  change (((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
    ((Multiset.toFinset_card_of_nodup
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm i : ℂ) ∈
    (mvFamilySpecialization p z.1).roots.toFinset
  exact (e i).property

theorem mvSimpleRootEnumeration_injective {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    Function.Injective (mvSimpleRootEnumeration hp z) := by
  intro i j hij
  have hsub : ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm i =
      ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
      ((Multiset.toFinset_card_of_nodup
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
        (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm j := by
    exact Subtype.ext (by simpa [mvSimpleRootEnumeration] using hij)
  exact (Equiv.injective _ hsub)

theorem exists_mvSimpleRootEnumeration {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) (w : ℂ)
    (hw : (mvFamilySpecialization p z.1).eval w = 0) :
    ∃ i : Fin p.natDegree, mvSimpleRootEnumeration hp z i = w := by
  have hmem : w ∈ (mvFamilySpecialization p z.1).roots :=
    (mem_roots (hp.map (MvPolynomial.eval z.1)).ne_zero).mpr hw
  let e := ((mvFamilySpecialization p z.1).roots.toFinset.equivFinOfCardEq
    ((Multiset.toFinset_card_of_nodup
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).2).trans
      (mvRoots_card_nodup_of_mem_simpleRootBase hp z).1)).symm
  have hwfin : w ∈ (mvFamilySpecialization p z.1).roots.toFinset := by
    simpa using hmem
  refine ⟨e.symm ⟨w, hwfin⟩, ?_⟩
  simp [mvSimpleRootEnumeration, e]

/-- The point of the root cover attached to an enumerated root of a simple fiber. -/
noncomputable def mvSimpleRootCoverPoint {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) (i : Fin p.natDegree) : MvSimpleRootCover p :=
  ⟨(z, mvSimpleRootEnumeration hp z i), mvSimpleRootEnumeration_isRoot hp z i⟩

/-- One neighborhood of the base point supports all the finitely many local root branches. -/
theorem eventually_all_mvFamilyEquation_mvLocalRootBranch {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ i : Fin p.natDegree,
      mvFamilyEquation p (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0 := by
  exact eventually_all.2 fun i ↦
    eventually_mvFamilyEquation_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)

/-- Near the center, the finitely many root branches remain pairwise distinct. -/
theorem eventually_injective_mvLocalRootBranches {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, Function.Injective
      (fun i : Fin p.natDegree ↦ mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') := by
  have hpair : ∀ i j : Fin p.natDegree, i ≠ j →
      ∀ᶠ z' in 𝓝 z.1,
        mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z' ≠
          mvLocalRootBranch (mvSimpleRootCoverPoint hp z j) z' := by
    intro i j hij
    have hne : mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 -
        mvLocalRootBranch (mvSimpleRootCoverPoint hp z j) z.1 ≠ 0 := by
      have hi : mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 =
          mvSimpleRootEnumeration hp z i := by
        change mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)
          (mvSimpleRootCoverPoint hp z i).1.1.1 = _
        exact mvLocalRootBranch_apply_base _
      have hj : mvLocalRootBranch (mvSimpleRootCoverPoint hp z j) z.1 =
          mvSimpleRootEnumeration hp z j := by
        change mvLocalRootBranch (mvSimpleRootCoverPoint hp z j)
          (mvSimpleRootCoverPoint hp z j).1.1.1 = _
        exact mvLocalRootBranch_apply_base _
      rw [hi, hj]
      exact sub_ne_zero.mpr (fun h ↦ hij (mvSimpleRootEnumeration_injective hp z h))
    have hcont :=
      (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)).continuousAt.sub
        (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z j)).continuousAt
    filter_upwards [hcont.eventually (isOpen_compl_singleton.mem_nhds hne)] with z' hz
    exact sub_ne_zero.mp hz
  filter_upwards [eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    eventually_all.2 fun hij : i ≠ j ↦ hpair i j hij] with z' hz
  intro i j heq
  by_contra hij
  exact hz i j hij heq

/-- On a common neighborhood, the local branches exhaust every root of every fiber. -/
theorem eventually_exists_mvLocalRootBranch_eq_of_mvFamilyEquation_eq_zero
    {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ w : ℂ, mvFamilyEquation p (z', w) = 0 →
      ∃ i : Fin p.natDegree, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z' = w := by
  filter_upwards [eventually_all_mvFamilyEquation_mvLocalRootBranch hp z,
    eventually_injective_mvLocalRootBranches hp z] with z' hroot hinj
  intro w hw
  let q := mvFamilySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'
  let B : Finset ℂ := Finset.univ.image f
  have hq : q.Monic := hp.map (MvPolynomial.eval z')
  have hdegree : q.natDegree = p.natDegree := hp.natDegree_map (MvPolynomial.eval z')
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

/-- The simple-root base contains a neighborhood of each of its points. -/
theorem eventually_mem_mvSimpleRootBase {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
      (mvFamilySpecialization p z').derivative.eval w ≠ 0 := by
  filter_upwards [eventually_all_mvFamilyEquation_mvLocalRootBranch hp z,
    eventually_injective_mvLocalRootBranches hp z] with z' hroot hinj
  let q := mvFamilySpecialization p z'
  let f : Fin p.natDegree → ℂ :=
    fun i ↦ mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'
  let B : Finset ℂ := Finset.univ.image f
  have hq : q.Monic := hp.map (MvPolynomial.eval z')
  have hdegree : q.natDegree = p.natDegree := hp.natDegree_map (MvPolynomial.eval z')
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



theorem isOpen_mvSimpleRootBase {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) :
    IsOpen {z : Fin n → ℂ | ∀ w : ℂ, (mvFamilySpecialization p z).eval w = 0 →
      (mvFamilySpecialization p z).derivative.eval w ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact eventually_mem_mvSimpleRootBase hp ⟨z, hz⟩


theorem eventually_mem_clopen_mvLocalRootBranch_iff {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) (S : Set (MvSimpleRootCover p)) (hSopen : IsOpen S)
    (hSclosed : IsClosed S) (z : MvSimpleRootBase p) (i : Fin p.natDegree) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hroot : mvFamilyEquation p
        (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0),
      (⟨(⟨z', hbase⟩, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot⟩ :
          MvSimpleRootCover p) ∈ S ↔ mvSimpleRootCoverPoint hp z i ∈ S := by
  let U : Set (Fin n → ℂ) := {z' | (∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
      (mvFamilySpecialization p z').derivative.eval w ≠ 0) ∧
    mvFamilyEquation p (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0}
  have hU : U ∈ 𝓝 z.1 := inter_mem (eventually_mem_mvSimpleRootBase hp z)
    (eventually_mvFamilyEquation_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i))
  have hzU : z.1 ∈ U := by
    refine ⟨z.2, ?_⟩
    have hbranch : mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 =
        mvSimpleRootEnumeration hp z i := by
      simpa [mvSimpleRootCoverPoint] using
        mvLocalRootBranch_apply_base (mvSimpleRootCoverPoint hp z i)
    rw [mvFamilyEquation, hbranch]
    exact mvSimpleRootEnumeration_isRoot hp z i
  let g : U → MvSimpleRootCover p := fun x ↦
    ⟨(⟨x.1, x.2.1⟩, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) x.1), x.2.2⟩
  have hg : ContinuousAt g ⟨z.1, hzU⟩ := by
    apply ContinuousAt.codRestrict
    apply ContinuousAt.prodMk
    · exact continuousAt_subtype_val.codRestrict fun x ↦ x.2.1
    · have hbranch :=
        (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)).continuousAt
      have hbranch' : ContinuousAt (mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)) z.1 := by
        simpa [mvSimpleRootCoverPoint] using hbranch
      have hval : ContinuousAt ((↑) : U → (Fin n → ℂ)) ⟨z.1, hzU⟩ := continuousAt_subtype_val
      change ContinuousAt
        (mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) ∘ ((↑) : U → (Fin n → ℂ))) ⟨z.1, hzU⟩
      exact hbranch'.comp_of_eq hval rfl
  have hg_center : g ⟨z.1, hzU⟩ = mvSimpleRootCoverPoint hp z i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 = mvSimpleRootEnumeration hp z i
      exact mvLocalRootBranch_apply_base _
  have hmap : Filter.map ((↑) : U → (Fin n → ℂ)) (𝓝 ⟨z.1, hzU⟩) = 𝓝 z.1 :=
    map_nhds_subtype_coe_eq_nhds hzU hU
  by_cases hi : mvSimpleRootCoverPoint hp z i ∈ S
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



/-- The root cover on the principal open, in the form used by standard étale coordinates. -/
abbrev MvSimpleRootCoverOn {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (r : MvPolynomial (Fin n) ℂ) :=
  {zw : (Fin n → ℂ) × ℂ // mvFamilyEquation p zw = 0 ∧
    MvPolynomial.eval zw.1 r * (mvFamilySpecialization p zw.1).derivative.eval zw.2 ≠ 0}

/-- Clopen branch membership remains constant while the branch stays over `D(r)`. -/
theorem eventually_nonzero_and_mem_clopen_mvLocalRootBranch_iff {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootCover p))
    (hSopen : IsOpen S) (hSclosed : IsClosed S) (z : MvSimpleRootBase p)
    (hzr : MvPolynomial.eval z.1 r ≠ 0) (i : Fin p.natDegree) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hroot : mvFamilyEquation p
        (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0),
      MvPolynomial.eval z' r ≠ 0 ∧
        ((⟨(⟨z', hbase⟩, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot⟩ :
            MvSimpleRootCover p) ∈ S ↔ mvSimpleRootCoverPoint hp z i ∈ S) := by
  have hcont : ContinuousAt (fun z' : Fin n → ℂ ↦ MvPolynomial.eval z' r) z.1 :=
    (AnalyticOnNhd.eval_mvPolynomial r z.1 (Set.mem_univ _)).continuousAt
  have hnonzero : ∀ᶠ z' in 𝓝 z.1, MvPolynomial.eval z' r ≠ 0 :=
    hcont.eventually (isOpen_compl_singleton.mem_nhds hzr)
  filter_upwards [hnonzero,
    eventually_mem_clopen_mvLocalRootBranch_iff hp S hSopen hSclosed z i] with
      z' hz' hmem hbase hroot
  exact ⟨hz', hmem hbase hroot⟩


/-- Indices of the roots selected by a subset at the center fiber. -/
noncomputable def mvSelectedBranchIndices {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (S : Set (MvSimpleRootCover p)) (z : MvSimpleRootBase p) : Finset (Fin p.natDegree) := by
  classical
  exact Finset.univ.filter fun i ↦ mvSimpleRootCoverPoint hp z i ∈ S

/-- Selected branch indices in a nearby enumerated fiber. -/
noncomputable def mvSelectedBranchIndicesAt {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (S : Set (MvSimpleRootCover p)) (z : MvSimpleRootBase p) (z' : Fin n → ℂ)
    (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
      (mvFamilySpecialization p z').derivative.eval w ≠ 0)
    (hroot : ∀ i : Fin p.natDegree, mvFamilyEquation p
      (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0) :
    Finset (Fin p.natDegree) := by
  classical
  exact Finset.univ.filter fun i ↦
    (⟨(⟨z', hbase⟩, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot i⟩ :
      MvSimpleRootCover p) ∈ S

/-- The number of selected enumerated branches is locally constant for a clopen selection. -/
theorem eventually_card_selected_mvLocalRootBranches {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (S : Set (MvSimpleRootCover p)) (hSopen : IsOpen S) (hSclosed : IsClosed S)
    (z : MvSimpleRootBase p) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hroot : ∀ i : Fin p.natDegree, mvFamilyEquation p
        (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0),
      (mvSelectedBranchIndicesAt hp S z z' hbase hroot).card = (mvSelectedBranchIndices hp S z).card := by
  classical
  have hmem : ∀ᶠ z' in 𝓝 z.1, ∀ i : Fin p.natDegree,
      ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
          (mvFamilySpecialization p z').derivative.eval w ≠ 0)
        (hroot : mvFamilyEquation p
          (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0),
        ((⟨(⟨z', hbase⟩, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot⟩ :
          MvSimpleRootCover p) ∈ S ↔ mvSimpleRootCoverPoint hp z i ∈ S) :=
    eventually_all.2 fun i ↦
      eventually_mem_clopen_mvLocalRootBranch_iff hp S hSopen hSclosed z i
  filter_upwards [hmem] with z' hz hbase hroot
  congr 1
  ext i
  simp only [mvSelectedBranchIndicesAt, mvSelectedBranchIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hz i hbase (hroot i)


noncomputable def mvSimpleRootCoverOnPoint {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (z : MvSimpleRootBase p)
    (hzr : MvPolynomial.eval z.1 r ≠ 0) (i : Fin p.natDegree) : MvSimpleRootCoverOn p r := by
  refine ⟨(z.1, mvSimpleRootEnumeration hp z i), mvSimpleRootEnumeration_isRoot hp z i, ?_⟩
  exact mul_ne_zero hzr (z.2 _ (mvSimpleRootEnumeration_isRoot hp z i))

/-- Membership in a clopen part of the restricted cover is constant along each local branch. -/
theorem eventually_mem_clopen_mvSimpleRootCoverOn_iff {n : ℕ}
    {p : Polynomial (MvPolynomial (Fin n) ℂ)} (hp : p.Monic)
    (r : MvPolynomial (Fin n) ℂ) (S : Set (MvSimpleRootCoverOn p r))
    (hS : IsClopen S) (z : MvSimpleRootBase p) (hzr : MvPolynomial.eval z.1 r ≠ 0)
    (i : Fin p.natDegree) :
    ∀ᶠ z' in 𝓝 z.1, ∀ (hbase : ∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
        (mvFamilySpecialization p z').derivative.eval w ≠ 0)
      (hroot : mvFamilyEquation p
        (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0)
      (hr : MvPolynomial.eval z' r ≠ 0),
      (⟨(z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z'), hroot,
          mul_ne_zero hr (hbase _ hroot)⟩ : MvSimpleRootCoverOn p r) ∈ S ↔
        mvSimpleRootCoverOnPoint hp r z hzr i ∈ S := by
  let U : Set (Fin n → ℂ) := {z' | (∀ w : ℂ, (mvFamilySpecialization p z').eval w = 0 →
      (mvFamilySpecialization p z').derivative.eval w ≠ 0) ∧
    mvFamilyEquation p (z', mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z') = 0 ∧
    MvPolynomial.eval z' r ≠ 0}
  have hnonzero : ∀ᶠ z' in 𝓝 z.1, MvPolynomial.eval z' r ≠ 0 :=
    (AnalyticOnNhd.eval_mvPolynomial r z.1 (Set.mem_univ _)).continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds hzr)
  have hU : U ∈ 𝓝 z.1 := inter_mem (eventually_mem_mvSimpleRootBase hp z)
    (inter_mem (eventually_mvFamilyEquation_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i))
      hnonzero)
  have hzU : z.1 ∈ U := by
    refine ⟨z.2, ?_, hzr⟩
    change (mvFamilySpecialization p z.1).eval
      (mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1) = 0
    have hbranch : mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 =
        mvSimpleRootEnumeration hp z i := by
      simpa [mvSimpleRootCoverPoint] using
        mvLocalRootBranch_apply_base (mvSimpleRootCoverPoint hp z i)
    rw [hbranch]
    exact mvSimpleRootEnumeration_isRoot hp z i
  let g : U → MvSimpleRootCoverOn p r := fun x ↦
    ⟨(x.1, mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) x.1), x.2.2.1,
      mul_ne_zero x.2.2.2 (x.2.1 _ x.2.2.1)⟩
  have hg : ContinuousAt g ⟨z.1, hzU⟩ := by
    apply ContinuousAt.codRestrict
    apply ContinuousAt.prodMk
    · exact continuousAt_subtype_val
    · exact (differentiableAt_mvLocalRootBranch (mvSimpleRootCoverPoint hp z i)).continuousAt.comp_of_eq
        continuousAt_subtype_val rfl
  have hg_center : g ⟨z.1, hzU⟩ = mvSimpleRootCoverOnPoint hp r z hzr i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change mvLocalRootBranch (mvSimpleRootCoverPoint hp z i) z.1 =
          mvSimpleRootEnumeration hp z i
      exact mvLocalRootBranch_apply_base _
  have hmap : Filter.map ((↑) : U → (Fin n → ℂ)) (𝓝 ⟨z.1, hzU⟩) = 𝓝 z.1 :=
    map_nhds_subtype_coe_eq_nhds hzU hU
  by_cases hi : mvSimpleRootCoverOnPoint hp r z hzr i ∈ S
  · have hevent : ∀ᶠ x in 𝓝 (⟨z.1, hzU⟩ : U), g x ∈ S :=
      hg (hS.isOpen.mem_nhds (hg_center.symm ▸ hi))
    have hevent' : ∀ᶠ z' in 𝓝 z.1, ∀ hz' : z' ∈ U, g ⟨z', hz'⟩ ∈ S := by
      rw [← hmap, eventually_map]
      filter_upwards [hevent] with x hx
      intro hx'
      convert hx using 1
    filter_upwards [hU, hevent'] with z' hz' hmem hbase hroot hr
    exact ⟨fun _ ↦ hi, fun _ ↦ by simpa only [g, Subtype.ext_iff] using hmem hz'⟩
  · have hevent : ∀ᶠ x in 𝓝 (⟨z.1, hzU⟩ : U), g x ∈ Sᶜ :=
      hg (hS.isClosed.isOpen_compl.mem_nhds (by simpa [hg_center] using hi))
    have hevent' : ∀ᶠ z' in 𝓝 z.1, ∀ hz' : z' ∈ U, g ⟨z', hz'⟩ ∈ Sᶜ := by
      rw [← hmap, eventually_map]
      filter_upwards [hevent] with x hx
      intro hx'
      convert hx using 1
    filter_upwards [hU, hevent'] with z' hz' hmem hbase hroot hr
    exact ⟨fun h ↦ ((hmem hz') h).elim, fun h ↦ (hi h).elim⟩

end

end Polynomial
