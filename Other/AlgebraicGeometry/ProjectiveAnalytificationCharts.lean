/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveAnalytificationHomeomorph
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Constructions

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The standard affine charts of complex projective space

Mathlib puts no topology on `Projectivization`, and the repository's model of `ℙᴺ(ℂ)` uses the
quotient topology on it without ever producing the standard affine charts.  This file supplies
them: the `i`-th chart is the image of `ℂᴺ` under `z ↦ [insertNth i 1 z]`, and it is an open
embedding, so the chart domain is homeomorphic to `ℂᴺ`.  Transporting along
`projectivizationHomeomorph` gives the same charts on the analytification of scheme-theoretic
projective space.

The key topological input is that the tautological map from the nonzero vectors is an open
quotient map; the chart map is then open because the preimage of the image of an open set `W` is
the open set `{v | v i ≠ 0 ∧ chartRatio i v ∈ W}`.
-/

@[expose] public noncomputable section

open Set Topology CategoryTheory

namespace AlgebraicGeometry.ComplexProjectiveSpace

variable {n : ℕ}

/-! ### The tautological quotient map -/

/-- The tautological map from nonzero coordinate vectors onto the linear projectivization. -/
def projMk (v : {v : CoordinateSpace n // v ≠ 0}) :
    Projectivization ℂ (CoordinateSpace n) :=
  Projectivization.mk ℂ v.1 v.2

lemma projMk_apply (v : CoordinateSpace n) (hv : v ≠ 0) :
    projMk ⟨v, hv⟩ = Projectivization.mk ℂ v hv := rfl

lemma isQuotientMap_projMk : IsQuotientMap (projMk (n := n)) :=
  isQuotientMap_quotient_mk'

lemma continuous_projMk : Continuous (projMk (n := n)) :=
  isQuotientMap_projMk.continuous

lemma surjective_projMk : Function.Surjective (projMk (n := n)) :=
  isQuotientMap_projMk.surjective

lemma isOpen_iff_preimage_projMk {S : Set (Projectivization ℂ (CoordinateSpace n))} :
    IsOpen S ↔ IsOpen (projMk ⁻¹' S) :=
  isQuotientMap_projMk.isOpen_preimage.symm

/-- Scaling a nonzero vector by a nonzero scalar, as a self-map of the nonzero vectors. -/
def smulNonzero (a : ℂˣ) (v : {v : CoordinateSpace n // v ≠ 0}) :
    {v : CoordinateSpace n // v ≠ 0} :=
  ⟨(a : ℂ) • v.1, smul_ne_zero a.ne_zero v.2⟩

lemma continuous_smulNonzero (a : ℂˣ) : Continuous (smulNonzero (n := n) a) :=
  (((continuous_const_smul (a : ℂ)).comp continuous_subtype_val)).subtype_mk _

lemma projMk_smulNonzero (a : ℂˣ) (v : {v : CoordinateSpace n // v ≠ 0}) :
    projMk (smulNonzero a v) = projMk v :=
  (Projectivization.mk_eq_mk_iff' ℂ _ _ _ v.2).2 ⟨(a : ℂ), rfl⟩

lemma preimage_image_projMk (W : Set {v : CoordinateSpace n // v ≠ 0}) :
    projMk ⁻¹' (projMk '' W) = ⋃ a : ℂˣ, smulNonzero a ⁻¹' W := by
  ext v
  simp only [mem_preimage, mem_image, mem_iUnion]
  constructor
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ w.1 v.1 w.2 v.2).1 hwv
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact w.2 (by simpa using ha.symm)
    refine ⟨Units.mk0 a ha0, ?_⟩
    have : smulNonzero (Units.mk0 a ha0) v = w := Subtype.ext (by simpa [smulNonzero] using ha)
    rwa [this]
  · rintro ⟨a, ha⟩
    exact ⟨smulNonzero a v, ha, projMk_smulNonzero a v⟩

/-- The tautological map onto the projectivization is an open map. -/
lemma isOpenMap_projMk : IsOpenMap (projMk (n := n)) := by
  intro W hW
  rw [isOpen_iff_preimage_projMk, preimage_image_projMk]
  exact isOpen_iUnion fun a ↦ hW.preimage (continuous_smulNonzero a)

/-- The tautological map onto the projectivization is an open quotient map. -/
lemma isOpenQuotientMap_projMk : IsOpenQuotientMap (projMk (n := n)) :=
  ⟨surjective_projMk, continuous_projMk, isOpenMap_projMk⟩

/-! ### The standard affine charts -/

/-- The affine ratio coordinates of a coordinate vector in the `i`-th standard chart.  Off the
chart the formula is junk (division by zero), but it is still invariant under nonzero scaling,
so it descends to the projectivization. -/
def chartRatio (i : Fin (n + 1)) (v : CoordinateSpace n) : Fin n → ℂ :=
  fun j ↦ v (i.succAbove j) / v i

lemma chartRatio_smul (i : Fin (n + 1)) {t : ℂ} (ht : t ≠ 0) (v : CoordinateSpace n) :
    chartRatio i (t • v) = chartRatio i v := by
  funext j
  simp only [chartRatio, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ ht

/-- The affine slice `x_i = 1` consists of nonzero vectors. -/
lemma insertNth_one_ne_zero (i : Fin (n + 1)) (z : Fin n → ℂ) :
    (i.insertNth (1 : ℂ) z : CoordinateSpace n) ≠ 0 := by
  intro hc
  have h1 : (1 : ℂ) = 0 := by
    simpa [Fin.insertNth_apply_same] using congrFun hc i
  exact one_ne_zero h1

/-- The point of `ℙⁿ` with affine coordinates `z` in the `i`-th standard chart. -/
def chartPoint (i : Fin (n + 1)) (z : Fin n → ℂ) :
    Projectivization ℂ (CoordinateSpace n) :=
  Projectivization.mk ℂ (i.insertNth (1 : ℂ) z) (insertNth_one_ne_zero i z)

/-- The `i`-th standard affine chart of `ℙⁿ`. -/
def chartSet (i : Fin (n + 1)) : Set (Projectivization ℂ (CoordinateSpace n)) :=
  Set.range (chartPoint i)

/-- The affine coordinates of a point of `ℙⁿ` in the `i`-th standard chart. -/
def chartMap (i : Fin (n + 1)) :
    Projectivization ℂ (CoordinateSpace n) → (Fin n → ℂ) :=
  Projectivization.lift (fun v ↦ chartRatio i v.1) (by
    intro a b t hab
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by simpa using hab)
    show chartRatio i a.1 = chartRatio i b.1
    rw [show a.1 = t • b.1 from hab, chartRatio_smul i ht])

@[simp]
lemma chartMap_mk (i : Fin (n + 1)) (v : CoordinateSpace n) (hv : v ≠ 0) :
    chartMap i (Projectivization.mk ℂ v hv) = chartRatio i v := rfl

@[simp]
lemma chartMap_chartPoint (i : Fin (n + 1)) (z : Fin n → ℂ) :
    chartMap i (chartPoint i z) = z := by
  funext j
  simp [chartPoint, chartMap, chartRatio, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]

lemma injective_chartPoint (i : Fin (n + 1)) : Function.Injective (chartPoint (n := n) i) :=
  Function.LeftInverse.injective (chartMap_chartPoint i)

lemma insertNth_chartRatio (i : Fin (n + 1)) {v : CoordinateSpace n} (hv : v i ≠ 0) :
    i.insertNth (1 : ℂ) (chartRatio i v) = (v i)⁻¹ • v := by
  refine Fin.insertNth_eq_iff.2 ⟨?_, ?_⟩
  · simp [inv_mul_cancel₀ hv]
  · funext j
    simp [chartRatio, div_eq_inv_mul, Fin.removeNth_apply]

lemma chartPoint_chartRatio {i : Fin (n + 1)} {v : CoordinateSpace n} (hv0 : v ≠ 0)
    (hv : v i ≠ 0) :
    chartPoint i (chartRatio i v) = Projectivization.mk ℂ v hv0 := by
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ hv0).2 ⟨(v i)⁻¹, ?_⟩
  exact (insertNth_chartRatio i hv).symm

lemma preimage_chartSet (i : Fin (n + 1)) :
    projMk ⁻¹' chartSet (n := n) i = nonzeroVectorChart i := by
  ext v
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ v.1 _ v.2).1 hz
    have h1 : a * v.1 i = 1 := by
      simpa [Fin.insertNth_apply_same] using congrFun ha i
    show v.1 i ≠ 0
    intro hvi
    rw [hvi, mul_zero] at h1
    exact zero_ne_one h1
  · intro hv
    exact ⟨chartRatio i v.1, chartPoint_chartRatio v.2 hv⟩

lemma isOpen_chartSet (i : Fin (n + 1)) : IsOpen (chartSet (n := n) i) := by
  rw [isOpen_iff_preimage_projMk, preimage_chartSet]
  exact isOpen_nonzeroVectorChart i

lemma iUnion_chartSet : ⋃ i : Fin (n + 1), chartSet (n := n) i = Set.univ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  obtain ⟨v, hv⟩ := surjective_projMk p
  have : v ∈ ⋃ i : Fin (n + 1), nonzeroVectorChart i := by
    rw [iUnion_nonzeroVectorChart]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
  exact Set.mem_iUnion.2 ⟨i, hv ▸ (preimage_chartSet i ▸ hi : v ∈ projMk ⁻¹' chartSet i)⟩

lemma continuous_chartPoint (i : Fin (n + 1)) : Continuous (chartPoint (n := n) i) := by
  have hi : Continuous fun z : Fin n → ℂ ↦ (i.insertNth (1 : ℂ) z : CoordinateSpace n) := by
    refine continuous_pi fun k ↦ ?_
    refine Fin.succAboveCases i ?_ ?_ k
    · simpa [Fin.insertNth_apply_same] using continuous_const (y := (1 : ℂ))
    · intro j
      simpa [Fin.insertNth_apply_succAbove] using continuous_apply (A := fun _ : Fin n ↦ ℂ) j
  exact continuous_projMk.comp (hi.subtype_mk (insertNth_one_ne_zero i))

lemma continuousOn_chartRatio (i : Fin (n + 1)) :
    ContinuousOn (fun v : {v : CoordinateSpace n // v ≠ 0} ↦ chartRatio i v.1)
      (nonzeroVectorChart i) := by
  intro v hv
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_pi.2 fun j ↦ ?_
  have hnum : ContinuousAt
      (fun w : {v : CoordinateSpace n // v ≠ 0} ↦ w.1 (i.succAbove j)) v :=
    (((continuous_apply (i.succAbove j)).comp continuous_subtype_val)).continuousAt
  have hden : ContinuousAt (fun w : {v : CoordinateSpace n // v ≠ 0} ↦ w.1 i) v :=
    (((continuous_apply i).comp continuous_subtype_val)).continuousAt
  exact hnum.div hden hv

lemma preimage_image_chartPoint (i : Fin (n + 1)) (W : Set (Fin n → ℂ)) :
    projMk ⁻¹' (chartPoint i '' W) =
      nonzeroVectorChart i ∩ (fun v : {v : CoordinateSpace n // v ≠ 0} ↦ chartRatio i v.1) ⁻¹' W := by
  ext v
  constructor
  · rintro ⟨z, hz, hzv⟩
    have hmem : v ∈ projMk ⁻¹' chartSet i := ⟨z, hzv⟩
    have hvi : v.1 i ≠ 0 := by rwa [preimage_chartSet] at hmem
    refine ⟨hvi, ?_⟩
    have hz' : chartRatio i v.1 = z := by
      have h := congrArg (chartMap i) hzv
      rw [chartMap_chartPoint] at h
      exact h.symm
    rwa [Set.mem_preimage, hz']
  · rintro ⟨hvi, hw⟩
    exact ⟨chartRatio i v.1, hw, (chartPoint_chartRatio v.2 hvi).symm ▸ rfl⟩

/-- The `i`-th chart map is an open map: the cone over an open subset of the affine slice is
open among the nonzero vectors. -/
lemma isOpenMap_chartPoint (i : Fin (n + 1)) : IsOpenMap (chartPoint (n := n) i) := by
  intro W hW
  rw [isOpen_iff_preimage_projMk, preimage_image_chartPoint]
  exact (continuousOn_chartRatio i).isOpen_inter_preimage (isOpen_nonzeroVectorChart i) hW

/-- The `i`-th standard affine chart, as an equivalence with `ℂⁿ`. -/
def chartEquiv (i : Fin (n + 1)) : (Fin n → ℂ) ≃ chartSet (n := n) i where
  toFun z := ⟨chartPoint i z, ⟨z, rfl⟩⟩
  invFun p := chartMap i p.1
  left_inv z := by simp
  right_inv p := by
    obtain ⟨z, hz⟩ := p.2
    apply Subtype.ext
    simp [← hz]

/-- **The standard affine charts of `ℙⁿ(ℂ)`.**  The `i`-th chart domain `{x_i ≠ 0}` is
homeomorphic to `ℂⁿ`. -/
def chartHomeomorph (i : Fin (n + 1)) : (Fin n → ℂ) ≃ₜ chartSet (n := n) i :=
  (chartEquiv i).toHomeomorphOfContinuousOpen
    ((continuous_chartPoint i).subtype_mk _)
    (by
      intro W hW
      rw [(isOpen_chartSet i).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]
      have himg : Subtype.val '' (chartEquiv i '' W) = chartPoint i '' W := by
        ext p
        constructor
        · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨z, hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨chartPoint i z, ⟨z, rfl⟩⟩, ⟨z, hz, rfl⟩, rfl⟩
      rw [himg]
      exact isOpenMap_chartPoint i W hW)

@[simp]
lemma chartHomeomorph_apply (i : Fin (n + 1)) (z : Fin n → ℂ) :
    ((chartHomeomorph (n := n) i) z : Projectivization ℂ (CoordinateSpace n)) =
      chartPoint i z := rfl

@[simp]
lemma chartHomeomorph_symm_apply (i : Fin (n + 1)) (p : chartSet (n := n) i) :
    (chartHomeomorph (n := n) i).symm p = chartMap i p.1 := rfl

/-! ### The same charts on the analytification of scheme-theoretic projective space -/

/-- The `i`-th standard affine chart of `ℙᴺ(ℂ)^an`, transported along the homeomorphism with the
linear projectivization. -/
def complexPointChartSet (i : Fin (n + 1)) :
    Set (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
  projectivizationHomeomorph n '' chartSet i

lemma complexPointChartSet_eq (i : Fin (n + 1)) :
    complexPointChartSet (n := n) i = projectivizationToComplexPoint '' chartSet i := rfl

lemma isOpen_complexPointChartSet (i : Fin (n + 1)) :
    IsOpen (complexPointChartSet (n := n) i) :=
  (projectivizationHomeomorph n).isOpenMap _ (isOpen_chartSet i)

lemma iUnion_complexPointChartSet :
    ⋃ i : Fin (n + 1), complexPointChartSet (n := n) i = Set.univ := by
  simp only [complexPointChartSet, ← Set.image_iUnion, iUnion_chartSet, Set.image_univ]
  exact (projectivizationHomeomorph n).surjective.range_eq

/-- **The standard affine charts of the analytification of projective space.**  The `i`-th chart
domain is homeomorphic to `ℂᴺ`. -/
def complexPointChartHomeomorph (i : Fin (n + 1)) :
    (Fin n → ℂ) ≃ₜ complexPointChartSet (n := n) i :=
  (chartHomeomorph i).trans ((projectivizationHomeomorph n).image (chartSet i))

@[simp]
lemma complexPointChartHomeomorph_apply (i : Fin (n + 1)) (z : Fin n → ℂ) :
    ((complexPointChartHomeomorph (n := n) i) z :
        ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) =
      projectivizationToComplexPoint (chartPoint i z) := rfl

end AlgebraicGeometry.ComplexProjectiveSpace
