/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticRelativeIteratedSupportClass
public import Other.AlgebraicGeometry.HolomorphicClosedImmersionCharts

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension

/-!
# The iterated punctured normal-coordinate cover

For a smooth closed immersion of positive codimension `c + 1`, the complement
of the zero normal plane in a holomorphic flattening chart is covered by the
normal-coordinate nonvanishing opens.  Ordering those coordinates gives a
chain of `c` relative two-open covers.  Its deepest overlap is the locus where
all `c + 1` normal coordinates are nonzero, so all coordinate functions are
holomorphic units there.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X Y : Over (Spec (.of ℂ))) (i : Y ⟶ X) (m c : ℕ)
  [SmoothOfRelativeDimension m Y.hom]
  [SmoothOfRelativeDimension (m + (c + 1)) X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

noncomputable local instance normalCoordinateIteratedCoverIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ)) ω
      (ComplexPoint X) :=
  isManifold_omega X (m + (c + 1))

/-- The `j`th standard normal index, with the ambient subtraction displayed
in the type of the flattening chart. -/
def iteratedNormalIndex (j : Fin (c + 1)) :
    Fin ((m + (c + 1)) - m) :=
  Fin.cast (by omega) j

/-- The `j`th normal coordinate on the ambient variety, extended by the chart
formula outside the chart source. -/
def iteratedNormalCoordinate (j : Fin (c + 1))
    (y : ComplexPoint X) : ℂ :=
  (closedImmersionHolomorphicFlatteningChart X Y i m (m + (c + 1)) z y).2
    (iteratedNormalIndex m c j)

/-- The target locus on which the `j`th normal coordinate is nonzero. -/
def iteratedNormalCoordinateNonzeroTarget (j : Fin (c + 1)) :
    Set ((Fin m → ℂ) × (Fin ((m + (c + 1)) - m) → ℂ)) :=
  {v | v.2 (iteratedNormalIndex m c j) ≠ 0}

theorem isOpen_iteratedNormalCoordinateNonzeroTarget (j : Fin (c + 1)) :
    IsOpen (iteratedNormalCoordinateNonzeroTarget m c j) := by
  exact isOpen_ne.preimage
    ((continuous_apply (iteratedNormalIndex m c j)).comp continuous_snd)

/-- The actual analytic open where the `j`th normal coordinate is nonzero. -/
def iteratedNormalCoordinateNonzeroOpen (j : Fin (c + 1)) :
    Opens (ComplexPoint X) :=
  ⟨(closedImmersionHolomorphicFlatteningChart
      X Y i m (m + (c + 1)) z).source ∩
      (closedImmersionHolomorphicFlatteningChart
        X Y i m (m + (c + 1)) z) ⁻¹'
        iteratedNormalCoordinateNonzeroTarget m c j,
    (closedImmersionHolomorphicFlatteningChart
      X Y i m (m + (c + 1)) z).isOpen_inter_preimage
        (isOpen_iteratedNormalCoordinateNonzeroTarget m c j)⟩

@[simp]
theorem mem_iteratedNormalCoordinateNonzeroOpen_iff
    (j : Fin (c + 1)) (y : ComplexPoint X) :
    y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j ↔
      y ∈ (closedImmersionHolomorphicFlatteningChart
        X Y i m (m + (c + 1)) z).source ∧
      iteratedNormalCoordinate X Y i m c z j y ≠ 0 :=
  Iff.rfl

/-- The coordinates preceding `k` are all nonzero. -/
def iteratedNormalPrefixOpen (k : Fin (c + 1)) : Opens (ComplexPoint X) :=
  ⟨{y | ∀ j : Fin (c + 1), j < k →
      y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j}, by
    rw [show {y : ComplexPoint X | ∀ j : Fin (c + 1), j < k →
        y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j} =
      ⋂ j : {j : Fin (c + 1) // j.1 < k},
        (iteratedNormalCoordinateNonzeroOpen X Y i m c z j.1 :
          Set (ComplexPoint X)) by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h j ↦ h j.1 j.2,
        fun h j hj ↦ h ⟨j, hj⟩⟩]
    exact isOpen_iInter_of_finite fun j ↦
      (iteratedNormalCoordinateNonzeroOpen X Y i m c z j.1).2⟩

/-- At least one coordinate at or after `k` is nonzero. -/
def iteratedNormalSuffixOpen (k : Fin (c + 1)) : Opens (ComplexPoint X) :=
  ⟨{y | ∃ j : Fin (c + 1), k ≤ j ∧
      y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j}, by
    rw [show {y : ComplexPoint X | ∃ j : Fin (c + 1), k ≤ j ∧
        y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j} =
      ⋃ j : {j : Fin (c + 1) // k ≤ j.1},
        (iteratedNormalCoordinateNonzeroOpen X Y i m c z j.1 :
          Set (ComplexPoint X)) by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      exact ⟨fun ⟨j, hj, hy⟩ ↦ ⟨⟨j, hj⟩, hy⟩,
        fun ⟨j, hy⟩ ↦ ⟨j.1, j.2, hy⟩⟩]
    exact isOpen_iUnion fun j ↦
      (iteratedNormalCoordinateNonzeroOpen X Y i m c z j.1).2⟩

@[simp]
theorem mem_iteratedNormalPrefixOpen_iff
    (k : Fin (c + 1)) (y : ComplexPoint X) :
    y ∈ iteratedNormalPrefixOpen X Y i m c z k ↔
      ∀ j : Fin (c + 1), j < k →
        y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j := by
  rfl

@[simp]
theorem mem_iteratedNormalSuffixOpen_iff
    (k : Fin (c + 1)) (y : ComplexPoint X) :
    y ∈ iteratedNormalSuffixOpen X Y i m c z k ↔
      ∃ j : Fin (c + 1), k ≤ j ∧
        y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j := by
  rfl

/-- The `k`th ambient open: earlier coordinates are nonzero and at least one
remaining coordinate is nonzero. -/
def iteratedNormalAmbientOpen (k : Fin (c + 1)) :
    Opens (ComplexPoint X) :=
  iteratedNormalPrefixOpen X Y i m c z k ⊓
    iteratedNormalSuffixOpen X Y i m c z k

@[simp]
theorem mem_iteratedNormalAmbientOpen_iff
    (k : Fin (c + 1)) (y : ComplexPoint X) :
    y ∈ iteratedNormalAmbientOpen X Y i m c z k ↔
      y ∈ iteratedNormalPrefixOpen X Y i m c z k ∧
      y ∈ iteratedNormalSuffixOpen X Y i m c z k :=
  Iff.rfl

/-- The left member at step `k`, on which the next coordinate is nonzero. -/
def iteratedNormalLeftOpen (k : Fin c) : Opens (ComplexPoint X) :=
  iteratedNormalPrefixOpen X Y i m c z k.castSucc ⊓
    iteratedNormalCoordinateNonzeroOpen X Y i m c z k.castSucc

@[simp]
theorem mem_iteratedNormalLeftOpen_iff
    (k : Fin c) (y : ComplexPoint X) :
    y ∈ iteratedNormalLeftOpen X Y i m c z k ↔
      y ∈ iteratedNormalPrefixOpen X Y i m c z k.castSucc ∧
      y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z k.castSucc :=
  Iff.rfl

/-- The right member at step `k`, on which a strictly later coordinate is
nonzero. -/
def iteratedNormalRightOpen (k : Fin c) : Opens (ComplexPoint X) :=
  iteratedNormalPrefixOpen X Y i m c z k.castSucc ⊓
    iteratedNormalSuffixOpen X Y i m c z k.succ

@[simp]
theorem mem_iteratedNormalRightOpen_iff
    (k : Fin c) (y : ComplexPoint X) :
    y ∈ iteratedNormalRightOpen X Y i m c z k ↔
      y ∈ iteratedNormalPrefixOpen X Y i m c z k.castSucc ∧
      y ∈ iteratedNormalSuffixOpen X Y i m c z k.succ :=
  Iff.rfl

/-- The ordered relative Mayer--Vietoris cover of the punctured normal chart. -/
def analyticNormalCoordinateRelativeIteratedCover :
    AnalyticRelativeIteratedCover X c where
  ambient := iteratedNormalAmbientOpen X Y i m c z
  left := iteratedNormalLeftOpen X Y i m c z
  right := iteratedNormalRightOpen X Y i m c z
  cover k := by
    ext y
    change (y ∈ iteratedNormalLeftOpen X Y i m c z k ∨
        y ∈ iteratedNormalRightOpen X Y i m c z k) ↔
      y ∈ iteratedNormalAmbientOpen X Y i m c z k.castSucc
    rw [mem_iteratedNormalLeftOpen_iff, mem_iteratedNormalRightOpen_iff,
      mem_iteratedNormalAmbientOpen_iff,
      mem_iteratedNormalPrefixOpen_iff,
      mem_iteratedNormalSuffixOpen_iff]
    constructor
    · rintro (⟨hpre, hk⟩ | ⟨hpre, ⟨j, hj, hyj⟩⟩)
      · exact ⟨hpre, ⟨k.castSucc, le_rfl, hk⟩⟩
      · exact ⟨hpre, ⟨j, le_trans (Fin.castSucc_le_succ k) hj, hyj⟩⟩
    · rintro ⟨hpre, ⟨j, hj, hyj⟩⟩
      by_cases heq : j = k.castSucc
      · subst j
        exact Or.inl ⟨hpre, hyj⟩
      · refine Or.inr ⟨hpre, j, ?_, hyj⟩
        apply Fin.le_iff_val_le_val.mpr
        have hjv : k.val ≤ j.val := Fin.le_iff_val_le_val.mp hj
        have hne : j.val ≠ k.val := by
          intro h
          exact heq (Fin.ext h)
        change k.val + 1 ≤ j.val
        omega
  overlap k := by
    ext y
    change (y ∈ iteratedNormalLeftOpen X Y i m c z k ∧
        y ∈ iteratedNormalRightOpen X Y i m c z k) ↔
      y ∈ iteratedNormalAmbientOpen X Y i m c z k.succ
    rw [mem_iteratedNormalLeftOpen_iff, mem_iteratedNormalRightOpen_iff,
      mem_iteratedNormalAmbientOpen_iff,
      mem_iteratedNormalPrefixOpen_iff,
      mem_iteratedNormalSuffixOpen_iff]
    constructor
    · rintro ⟨⟨hpre, hk⟩, -, hsuf⟩
      refine ⟨?_, hsuf⟩
      intro j hj
      by_cases heq : j = k.castSucc
      · subst j
        exact hk
      · apply hpre j
        have hjv : j.val < k.val + 1 := by
          exact_mod_cast hj
        have hne : j.val ≠ k.val := by
          intro h
          exact heq (Fin.ext h)
        change j.val < k.val
        omega
    · rintro ⟨hpre, hsuf⟩
      refine ⟨⟨?_, ?_⟩, ?_, hsuf⟩
      · intro j hj
        exact hpre j (hj.trans (show k.castSucc < k.succ from Fin.castSucc_lt_succ))
      · exact hpre k.castSucc (show k.castSucc < k.succ from Fin.castSucc_lt_succ)
      · intro j hj
        exact hpre j (hj.trans (show k.castSucc < k.succ from Fin.castSucc_lt_succ))

/-! ### The terminal coordinate units -/

/-- The first ambient open is precisely the locus in the flattening-chart
source where at least one normal coordinate is nonzero. -/
theorem mem_analyticNormalCoordinateRelativeIteratedCover_ambient_zero_iff
    (y : ComplexPoint X) :
    y ∈ (analyticNormalCoordinateRelativeIteratedCover X Y i m c z).ambient 0 ↔
      ∃ j : Fin (c + 1),
        y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j := by
  change y ∈ iteratedNormalAmbientOpen X Y i m c z 0 ↔ _
  rw [show (0 : Fin (c + 1)) = ⟨0, Nat.zero_lt_succ c⟩ by rfl,
    mem_iteratedNormalAmbientOpen_iff,
    mem_iteratedNormalPrefixOpen_iff,
    mem_iteratedNormalSuffixOpen_iff]
  simp

/-- On the deepest open every normal coordinate is nonzero. -/
theorem mem_analyticNormalCoordinateRelativeIteratedCover_ambient_last_iff
    (y : ComplexPoint X) :
    y ∈ (analyticNormalCoordinateRelativeIteratedCover X Y i m c z).ambient
        ⟨c, Nat.lt_succ_self c⟩ ↔
      ∀ j : Fin (c + 1),
        y ∈ iteratedNormalCoordinateNonzeroOpen X Y i m c z j := by
  change y ∈ iteratedNormalAmbientOpen X Y i m c z
    ⟨c, Nat.lt_succ_self c⟩ ↔ _
  rw [mem_iteratedNormalAmbientOpen_iff,
    mem_iteratedNormalPrefixOpen_iff,
    mem_iteratedNormalSuffixOpen_iff]
  constructor
  · rintro ⟨hpre, ⟨j, hj, hyj⟩⟩ k
    by_cases hk : k = ⟨c, Nat.lt_succ_self c⟩
    · subst k
      have hj' : j = ⟨c, Nat.lt_succ_self c⟩ := by
        apply Fin.ext
        change j.val = c
        have hjv : c ≤ j.val := Fin.le_iff_val_le_val.mp hj
        omega
      simpa [hj'] using hyj
    · exact hpre k (by
        apply Fin.lt_iff_val_lt_val.mpr
        change k.val < c
        have hkval : k.val ≠ c := by
          intro h
          exact hk (Fin.ext h)
        omega)
  · intro h
    refine ⟨?_, ⟨⟨c, Nat.lt_succ_self c⟩, le_rfl, h _⟩⟩
    intro j hj
    exact h j

/-- The deepest all-coordinate-nonzero open lies in the holomorphic
flattening-chart source. -/
theorem analyticNormalCoordinateRelativeIteratedCover_ambient_last_subset_source :
    ((analyticNormalCoordinateRelativeIteratedCover X Y i m c z).ambient
      ⟨c, Nat.lt_succ_self c⟩ : Set (ComplexPoint X)) ⊆
      (closedImmersionHolomorphicFlatteningChart
        X Y i m (m + (c + 1)) z).source := by
  intro y hy
  have hlast :=
    (mem_analyticNormalCoordinateRelativeIteratedCover_ambient_last_iff
      X Y i m c z y).mp hy ⟨c, Nat.lt_succ_self c⟩
  exact (mem_iteratedNormalCoordinateNonzeroOpen_iff
    X Y i m c z _ y).mp hlast |>.1

/-- Every standard normal coordinate is holomorphic throughout the selected
flattening-chart source. -/
theorem contMDiffAt_iteratedNormalCoordinate
    (j : Fin (c + 1)) {y : ComplexPoint X}
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart
      X Y i m (m + (c + 1)) z).source) :
    ContMDiffAt (modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (iteratedNormalCoordinate X Y i m c z j) y := by
  let A := closedImmersionNormalCoordinateChange
    X Y i m (m + (c + 1)) z
  have hchart : ContMDiffAt
      (modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ))
      (modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ)) ω
      (extChartAt (modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ))
        (Point.map i z)) y := by
    apply contMDiffAt_extChartAt'
    exact hy.1.1
  have hAcd : ContDiffAt ℂ ω A
      (localChart X (m + (c + 1)) (Point.map i z) y) :=
    (closedImmersionHolomorphicFlatteningChart_analytic
      X Y i m (m + (c + 1)) z y hy).1.contDiffAt
  have hA : ContMDiffAt
      (modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ))
      (modelWithCornersSelf ℂ
        ((Fin m → ℂ) × (Fin ((m + (c + 1)) - m) → ℂ))) ω
      A (localChart X (m + (c + 1)) (Point.map i z) y) :=
    hAcd.contMDiffAt
  have hcomp := hA.comp y hchart
  let L : ((Fin m → ℂ) ×
      (Fin ((m + (c + 1)) - m) → ℂ)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (iteratedNormalIndex m c j)).comp
      (ContinuousLinearMap.snd ℂ (Fin m → ℂ)
        (Fin ((m + (c + 1)) - m) → ℂ))
  have heval := L.contMDiffAt.comp y hcomp
  change ContMDiffAt
    (modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ))
    (modelWithCornersSelf ℂ ℂ) ω
      (fun x ↦ (A (localChart X (m + (c + 1)) (Point.map i z) x)).2
        (iteratedNormalIndex m c j)) y
  simpa [L, Function.comp_def] using heval

/-- The `j`th coordinate as a holomorphic function on the terminal overlap. -/
def iteratedNormalCoordinateSection (j : Fin (c + 1)) :
    OpenHolomorphicFunctions X (m + (c + 1))
      (.op ((analyticNormalCoordinateRelativeIteratedCover
        X Y i m c z).ambient ⟨c, Nat.lt_succ_self c⟩)) := by
  exact ⟨fun y ↦ iteratedNormalCoordinate X Y i m c z j y,
    fun y ↦ (contMDiffAt_subtype_iff
      (I := modelWithCornersSelf ℂ (Fin (m + (c + 1)) → ℂ))
      (I' := modelWithCornersSelf ℂ ℂ)
      (U := (analyticNormalCoordinateRelativeIteratedCover
        X Y i m c z).ambient ⟨c, Nat.lt_succ_self c⟩)
      (f := iteratedNormalCoordinate X Y i m c z j)
      (x := y)).mpr
        (contMDiffAt_iteratedNormalCoordinate X Y i m c z j
          (analyticNormalCoordinateRelativeIteratedCover_ambient_last_subset_source
            X Y i m c z y.2))⟩

theorem iteratedNormalCoordinateSection_ne_zero
    (j : Fin (c + 1))
    (y : (analyticNormalCoordinateRelativeIteratedCover
      X Y i m c z).ambient ⟨c, Nat.lt_succ_self c⟩) :
    (iteratedNormalCoordinateSection X Y i m c z j).1 y ≠ 0 := by
  have hj :=
    (mem_analyticNormalCoordinateRelativeIteratedCover_ambient_last_iff
      X Y i m c z y.1).mp y.2 j
  exact (mem_iteratedNormalCoordinateNonzeroOpen_iff
    X Y i m c z j y.1).mp hj |>.2

/-- The family of all normal coordinates as holomorphic units on the deepest
overlap `(C*)^(c+1)`. -/
def iteratedNormalCoordinateUnits :
    Fin (c + 1) →
      (OpenHolomorphicFunctions X (m + (c + 1))
        (.op ((analyticNormalCoordinateRelativeIteratedCover
          X Y i m c z).ambient ⟨c, Nat.lt_succ_self c⟩)))ˣ :=
  fun j ↦
    { val := iteratedNormalCoordinateSection X Y i m c z j
      inv := ⟨fun y ↦
          ((iteratedNormalCoordinateSection X Y i m c z j).1 y)⁻¹,
        (holomorphicFunctionSheaf_section_analytic X (m + (c + 1))
          (iteratedNormalCoordinateSection X Y i m c z j)).inv₀
            (iteratedNormalCoordinateSection_ne_zero X Y i m c z j)⟩
      val_inv := by
        apply ContMDiffMap.ext
        intro y
        exact mul_inv_cancel₀
          (iteratedNormalCoordinateSection_ne_zero X Y i m c z j y)
      inv_val := by
        apply ContMDiffMap.ext
        intro y
        exact inv_mul_cancel₀
          (iteratedNormalCoordinateSection_ne_zero X Y i m c z j y) }

/-! ### The concrete supported filtered Thom candidate -/

variable [IsIntegral X.left] [Smooth X.hom]

/-- The intrinsic dimension agrees with the ambient dimension used to build
the normal chart. -/
theorem dim_eq_iteratedNormal_ambient :
    dim X.left = m + (c + 1) := by
  rw [TopologicalSpace.dim_eq_krullDim,
    SmoothOfRelativeDimension.orderKrullDim_eq_complex
      (f := X.hom) (d := m + (c + 1))]
  change WithBot.unbotD 0 (↑(m + (c + 1)) : WithBot ℕ) = m + (c + 1)
  exact WithBot.unbotD_coe 0 (m + (c + 1))

/-- Transport a holomorphic unit across an equality between two displayed
smooth relative dimensions. -/
def openHolomorphicFunctionUnitOfDimensionEq
    {d e : ℕ}
    (hd : SmoothOfRelativeDimension d X.hom)
    (he : SmoothOfRelativeDimension e X.hom)
    (h : d = e) (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (OpenHolomorphicFunctions X d (.op U))ˣ) :
    (OpenHolomorphicFunctions X e (.op U))ˣ := by
  subst e
  exact u

/-- The terminal coordinate units transported to the intrinsic-dimensional
holomorphic-function sheaf used by the de Rham complex. -/
def iteratedNormalCoordinateUnitsIntrinsic :
    Fin (c + 1) →
      (OpenHolomorphicFunctions X (dim X.left)
        (.op ((analyticNormalCoordinateRelativeIteratedCover
          X Y i m c z).ambient ⟨c, Nat.lt_succ_self c⟩)))ˣ := by
  have hd : dim X.left = m + (c + 1) :=
    dim_eq_iteratedNormal_ambient (X := X) (m := m) (c := c)
  exact fun j ↦ openHolomorphicFunctionUnitOfDimensionEq X
    (inferInstance : SmoothOfRelativeDimension (m + (c + 1)) X.hom)
    (inferInstance : SmoothOfRelativeDimension (dim X.left) X.hom)
    hd.symm ((analyticNormalCoordinateRelativeIteratedCover
      X Y i m c z).ambient ⟨c, Nat.lt_succ_self c⟩)
    (iteratedNormalCoordinateUnits X Y i m c z j)

/-- The actual supported `F^(c+1)` class obtained from the ordered normal
coordinate cover and `dlog z₀ ∧ ⋯ ∧ dlog z_c`. -/
def analyticNormalCoordinateLogarithmicSupportedThomClass :
    SupportedFilteredDeRhamHypercohomology X
      ((analyticNormalCoordinateRelativeIteratedCover
        X Y i m c z).ambient 0).compl
      ((c + 1 : ℕ) : ℤ) (2 * ((c + 1 : ℕ) : ℤ)) :=
  analyticRelativeIteratedLogarithmicSupportedThomClass X rfl
    (analyticNormalCoordinateRelativeIteratedCover X Y i m c z)
    (iteratedNormalCoordinateUnitsIntrinsic X Y i m c z)

/-- The full supported de Rham image of the concrete normal-coordinate Thom
candidate. -/
def analyticNormalCoordinateLogarithmicSupportedThomDeRhamClass :
    SupportedDeRhamHypercohomology X
      ((analyticNormalCoordinateRelativeIteratedCover
        X Y i m c z).ambient 0).compl
      (2 * ((c + 1 : ℕ) : ℤ)) :=
  analyticRelativeIteratedLogarithmicSupportedThomDeRhamClass X rfl
    (analyticNormalCoordinateRelativeIteratedCover X Y i m c z)
    (iteratedNormalCoordinateUnitsIntrinsic X Y i m c z)

end AlgebraicGeometry.ComplexPoint
