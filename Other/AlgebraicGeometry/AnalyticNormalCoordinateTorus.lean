/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticNormalCoordinateIteratedCover
public import Other.AlgebraicTopology.NormalProjectionCoclass

/-!
# The positively oriented torus in a normal-coordinate overlap

The deepest overlap of `analyticNormalCoordinateRelativeIteratedCover` contains
the radial image of the standard real `(c+1)`-torus.  Every normal-coordinate
unit restricts there to a positive constant times its corresponding standard
one-turn exponential.  This supplies the exact geometric normalization needed
by a future iterated residue/de Rham comparison.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open Point AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ))) (i : Y ⟶ X) (m c : ℕ)
  [SmoothOfRelativeDimension m Y.hom]
  [SmoothOfRelativeDimension (m + (c + 1)) X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- The standard coordinatewise positive unit torus in the normal space. -/
def iteratedNormalTorusVector (t : Fin (c + 1) → ℝ) :
    Fin ((m + (c + 1)) - m) → ℂ :=
  fun j ↦ Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
    ((t (Fin.cast (by omega) j) : ℝ) : ℂ))

@[simp]
theorem iteratedNormalTorusVector_apply_index
    (t : Fin (c + 1) → ℝ) (j : Fin (c + 1)) :
    iteratedNormalTorusVector m c t (iteratedNormalIndex m c j) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t j : ℂ)) := by
  simp [iteratedNormalTorusVector, iteratedNormalIndex]

theorem iteratedNormalTorusVector_apply_ne_zero
    (t : Fin (c + 1) → ℝ)
    (j : Fin ((m + (c + 1)) - m)) :
    iteratedNormalTorusVector m c t j ≠ 0 :=
  Complex.exp_ne_zero _

theorem continuous_iteratedNormalTorusVector :
    Continuous (iteratedNormalTorusVector m c) := by
  unfold iteratedNormalTorusVector
  apply continuous_pi
  intro j
  fun_prop

@[simp]
theorem norm_iteratedNormalTorusVector (t : Fin (c + 1) → ℝ) :
    ‖iteratedNormalTorusVector m c t‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [iteratedNormalTorusVector, Complex.norm_exp]
    simp
  · have h := norm_le_pi_norm (iteratedNormalTorusVector m c t)
      (iteratedNormalIndex m c ⟨0, Nat.zero_lt_succ c⟩)
    calc
      1 = ‖Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          (t ⟨0, Nat.zero_lt_succ c⟩ : ℂ))‖ := by
        rw [Complex.norm_exp]
        simp
      _ ≤ ‖iteratedNormalTorusVector m c t‖ := by
        simpa using h

@[simp]
theorem norm_iteratedNormalTorusInput (t : Fin (c + 1) → ℝ) :
    ‖((0 : Fin m → ℂ), iteratedNormalTorusVector m c t)‖ = 1 := by
  simp [Prod.norm_def, norm_iteratedNormalTorusVector]

/-- The radial compression of the standard torus into the selected
holomorphic flattening chart. -/
def iteratedNormalTorusPoint (t : Fin (c + 1) → ℝ) : ComplexPoint X :=
  (flattenedSupportHomeomorph (Fin m → ℂ) ((m + (c + 1)) - m)
    (closedImmersionHolomorphicFlatteningChart
      X Y i m (m + (c + 1)) z)
    (Point.map i z)
    (closedImmersionHolomorphicFlatteningChart_mem_source
      X Y i m (m + (c + 1)) z)
      (0, iteratedNormalTorusVector m c t)).1

theorem iteratedNormalTorusPoint_mem_source (t : Fin (c + 1) → ℝ) :
    iteratedNormalTorusPoint X Y i m c z t ∈
      (closedImmersionHolomorphicFlatteningChart
        X Y i m (m + (c + 1)) z).source := by
  exact flattenedSupportNeighborhood_subset_source
    (Fin m → ℂ) ((m + (c + 1)) - m)
    (closedImmersionHolomorphicFlatteningChart
      X Y i m (m + (c + 1)) z)
    (Point.map i z)
    (closedImmersionHolomorphicFlatteningChart_mem_source
      X Y i m (m + (c + 1)) z)
    ((flattenedSupportHomeomorph
      (Fin m → ℂ) ((m + (c + 1)) - m)
      (closedImmersionHolomorphicFlatteningChart
        X Y i m (m + (c + 1)) z)
      (Point.map i z)
      (closedImmersionHolomorphicFlatteningChart_mem_source
        X Y i m (m + (c + 1)) z)
      (0, iteratedNormalTorusVector m c t)).property)

/-- Every normal coordinate has the exact positive radial normalization on
the torus. -/
theorem iteratedNormalCoordinate_torusPoint
    (t : Fin (c + 1) → ℝ) (j : Fin (c + 1)) :
    iteratedNormalCoordinate X Y i m c z j
        (iteratedNormalTorusPoint X Y i m c z t) =
      ((flattenedSupportRadius (Fin m → ℂ) ((m + (c + 1)) - m)
          (closedImmersionHolomorphicFlatteningChart
            X Y i m (m + (c + 1)) z)
          (Point.map i z)
          (closedImmersionHolomorphicFlatteningChart_mem_source
            X Y i m (m + (c + 1)) z)) *
        (Real.sqrt 2)⁻¹) •
          Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t j : ℂ)) := by
  let e := closedImmersionHolomorphicFlatteningChart
    X Y i m (m + (c + 1)) z
  let x := Point.map i z
  let hx := closedImmersionHolomorphicFlatteningChart_mem_source
    X Y i m (m + (c + 1)) z
  let r := flattenedSupportRadius
    (Fin m → ℂ) ((m + (c + 1)) - m) e x hx
  change (e ((flattenedSupportHomeomorph
      (Fin m → ℂ) ((m + (c + 1)) - m) e x hx)
        (0, iteratedNormalTorusVector m c t)).1).2
          (iteratedNormalIndex m c j) = _
  rw [flattenedSupportHomeomorph_coordinates
    (Fin m → ℂ) ((m + (c + 1)) - m) e x hx
      (0, iteratedNormalTorusVector m c t)]
  rw [OpenPartialHomeomorph.univBall, dif_pos
    (flattenedSupportRadius_pos
      (Fin m → ℂ) ((m + (c + 1)) - m) e x hx)]
  change (r • ((Real.sqrt (1 +
      ‖((0 : Fin m → ℂ), iteratedNormalTorusVector m c t)‖ ^ 2))⁻¹ •
        ((0 : Fin m → ℂ), iteratedNormalTorusVector m c t)) + e x).2
          (iteratedNormalIndex m c j) = _
  rw [norm_iteratedNormalTorusInput]
  dsimp [r, e, x, hx]
  simp
  ring_nf

theorem iteratedNormalCoordinate_torusPoint_ne_zero
    (t : Fin (c + 1) → ℝ) (j : Fin (c + 1)) :
    iteratedNormalCoordinate X Y i m c z j
      (iteratedNormalTorusPoint X Y i m c z t) ≠ 0 := by
  rw [iteratedNormalCoordinate_torusPoint]
  apply smul_ne_zero
  · exact mul_ne_zero
      (ne_of_gt (flattenedSupportRadius_pos
        (Fin m → ℂ) ((m + (c + 1)) - m)
        (closedImmersionHolomorphicFlatteningChart
          X Y i m (m + (c + 1)) z)
        (Point.map i z)
        (closedImmersionHolomorphicFlatteningChart_mem_source
          X Y i m (m + (c + 1)) z)))
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)))
  · exact Complex.exp_ne_zero _

/-- The radial torus as a map into the deepest all-coordinate-nonzero open. -/
def iteratedNormalTorus (t : Fin (c + 1) → ℝ) :
    (analyticNormalCoordinateRelativeIteratedCover
      X Y i m c z).ambient ⟨c, Nat.lt_succ_self c⟩ :=
  ⟨iteratedNormalTorusPoint X Y i m c z t,
    (mem_analyticNormalCoordinateRelativeIteratedCover_ambient_last_iff
      X Y i m c z _).mpr fun j ↦
        (mem_iteratedNormalCoordinateNonzeroOpen_iff
          X Y i m c z j _).mpr
            ⟨iteratedNormalTorusPoint_mem_source X Y i m c z t,
              iteratedNormalCoordinate_torusPoint_ne_zero X Y i m c z t j⟩⟩

theorem continuous_iteratedNormalTorus :
    Continuous (iteratedNormalTorus X Y i m c z) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : Fin (c + 1) → ℝ ↦
    ((flattenedSupportHomeomorph
      (Fin m → ℂ) ((m + (c + 1)) - m)
      (closedImmersionHolomorphicFlatteningChart
        X Y i m (m + (c + 1)) z)
      (Point.map i z)
      (closedImmersionHolomorphicFlatteningChart_mem_source
        X Y i m (m + (c + 1)) z))
      (0, iteratedNormalTorusVector m c t)).1)
  simpa [Function.comp_def] using
    continuous_subtype_val.comp
      ((flattenedSupportHomeomorph
        (Fin m → ℂ) ((m + (c + 1)) - m)
        (closedImmersionHolomorphicFlatteningChart
          X Y i m (m + (c + 1)) z)
        (Point.map i z)
        (closedImmersionHolomorphicFlatteningChart_mem_source
          X Y i m (m + (c + 1)) z)).continuous.comp
            (continuous_const.prodMk (continuous_iteratedNormalTorusVector m c)))

/-- On the radial torus, the `j`th holomorphic unit is exactly a positive
constant times the standard positive exponential in the `j`th variable. -/
theorem iteratedNormalCoordinateUnit_on_torus
    (t : Fin (c + 1) → ℝ) (j : Fin (c + 1)) :
    (iteratedNormalCoordinateUnits X Y i m c z j).val.1
        (iteratedNormalTorus X Y i m c z t) =
      (iteratedNormalCoordinateUnits X Y i m c z j).val.1
          (iteratedNormalTorus X Y i m c z 0) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t j : ℂ)) := by
  change iteratedNormalCoordinate X Y i m c z j
      (iteratedNormalTorusPoint X Y i m c z t) =
    iteratedNormalCoordinate X Y i m c z j
        (iteratedNormalTorusPoint X Y i m c z 0) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t j : ℂ))
  rw [iteratedNormalCoordinate_torusPoint,
    iteratedNormalCoordinate_torusPoint]
  simp

end AlgebraicGeometry.ComplexPoint
