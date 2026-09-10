/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicUnitObstruction
public import Other.AlgebraicGeometry.HolomorphicClosedImmersionCharts
public import Other.AlgebraicTopology.NormalProjectionCoclass

/-!
# The punctured normal-coordinate unit in codimension one

On the holomorphic flattening chart of a smooth codimension-one closed
immersion, the unique normal coordinate is a holomorphic function.  Removing
its zero locus makes it an actual holomorphic unit.  This file also constructs
the radial normal loop on which that unit makes exactly one positive turn.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ))) (i : Y ⟶ X) (m : ℕ)
  [SmoothOfRelativeDimension m Y.hom]
  [SmoothOfRelativeDimension (m + 1) X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

noncomputable local instance codimensionOneNormalUnitIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin (m + 1) → ℂ)) ω
      (ComplexPoint X) :=
  isManifold_omega X (m + 1)

/-- The unique index of the one-dimensional normal coordinate. -/
def codimensionOneNormalIndex : Fin ((m + 1) - m) :=
  ⟨0, by omega⟩

/-- The normal-coordinate locus in the flattening-chart target on which the
unique normal coordinate is nonzero. -/
def codimensionOneNormalNonzeroTarget :
    Set ((Fin m → ℂ) × (Fin ((m + 1) - m) → ℂ)) :=
  {v | v.2 (codimensionOneNormalIndex m) ≠ 0}

theorem isOpen_codimensionOneNormalNonzeroTarget :
    IsOpen (codimensionOneNormalNonzeroTarget m) := by
  exact isOpen_ne.preimage
    ((continuous_apply (codimensionOneNormalIndex m)).comp continuous_snd)

/-- The punctured holomorphic normal chart, as an actual analytic open in the
ambient variety. -/
def codimensionOnePuncturedNormalOpen : Opens (ComplexPoint X) :=
  ⟨(closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z).source ∩
      (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z) ⁻¹'
        codimensionOneNormalNonzeroTarget m,
    (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z).isOpen_inter_preimage
      (isOpen_codimensionOneNormalNonzeroTarget m)⟩

theorem codimensionOnePuncturedNormalOpen_subset_source :
    (codimensionOnePuncturedNormalOpen X Y i m z : Set (ComplexPoint X)) ⊆
      (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z).source :=
  fun _ h ↦ h.1

/-- The unique normal-coordinate function, extended arbitrarily outside the
flattening-chart source. -/
def codimensionOneNormalCoordinate (y : ComplexPoint X) : ℂ :=
  (closedImmersionNormalCoordinateChange X Y i m (m + 1) z
    (localChart X (m + 1) (Point.map i z) y)).2
      (codimensionOneNormalIndex m)

@[simp]
theorem codimensionOneNormalCoordinate_eq_flatteningChart (y : ComplexPoint X) :
    codimensionOneNormalCoordinate X Y i m z y =
      (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z y).2
        (codimensionOneNormalIndex m) :=
  rfl

/-- The normal coordinate is analytic at every point of the holomorphic
flattening-chart source. -/
theorem contMDiffAt_codimensionOneNormalCoordinate
    {y : ComplexPoint X}
    (hy : y ∈
      (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z).source) :
    ContMDiffAt (modelWithCornersSelf ℂ (Fin (m + 1) → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (codimensionOneNormalCoordinate X Y i m z) y := by
  let A := closedImmersionNormalCoordinateChange X Y i m (m + 1) z
  let e := closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z
  have hchart : ContMDiffAt
      (modelWithCornersSelf ℂ (Fin (m + 1) → ℂ))
      (modelWithCornersSelf ℂ (Fin (m + 1) → ℂ)) ω
      (extChartAt (modelWithCornersSelf ℂ (Fin (m + 1) → ℂ))
        (Point.map i z)) y := by
    apply contMDiffAt_extChartAt'
    exact hy.1.1
  have hAcd : ContDiffAt ℂ ω A
      (localChart X (m + 1) (Point.map i z) y) :=
    (closedImmersionHolomorphicFlatteningChart_analytic
      X Y i m (m + 1) z y hy).1.contDiffAt
  have hA : ContMDiffAt
      (modelWithCornersSelf ℂ (Fin (m + 1) → ℂ))
      (modelWithCornersSelf ℂ
        ((Fin m → ℂ) × (Fin ((m + 1) - m) → ℂ))) ω
      A (localChart X (m + 1) (Point.map i z) y) :=
    hAcd.contMDiffAt
  have hcomp := hA.comp y hchart
  let L : ((Fin m → ℂ) × (Fin ((m + 1) - m) → ℂ)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (codimensionOneNormalIndex m)).comp
      (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin ((m + 1) - m) → ℂ))
  have heval := L.contMDiffAt.comp y hcomp
  change ContMDiffAt (modelWithCornersSelf ℂ (Fin (m + 1) → ℂ))
    (modelWithCornersSelf ℂ ℂ) ω
      (fun x ↦ (A (localChart X (m + 1) (Point.map i z) x)).2
        (codimensionOneNormalIndex m)) y
  simpa [L, Function.comp_def] using heval

/-- The unique normal coordinate is a holomorphic section on the punctured
normal chart. -/
def codimensionOneNormalCoordinateSection :
    OpenHolomorphicFunctions X (m + 1)
      (.op (codimensionOnePuncturedNormalOpen X Y i m z)) := by
  exact ⟨fun y ↦ codimensionOneNormalCoordinate X Y i m z y,
    fun y ↦ (contMDiffAt_subtype_iff
      (I := modelWithCornersSelf ℂ (Fin (m + 1) → ℂ))
      (I' := modelWithCornersSelf ℂ ℂ)
      (U := codimensionOnePuncturedNormalOpen X Y i m z)
      (f := codimensionOneNormalCoordinate X Y i m z)
      (x := y)).mpr
        (contMDiffAt_codimensionOneNormalCoordinate X Y i m z y.2.1)⟩

theorem codimensionOneNormalCoordinateSection_ne_zero
    (y : codimensionOnePuncturedNormalOpen X Y i m z) :
    (codimensionOneNormalCoordinateSection X Y i m z).1 y ≠ 0 := by
  change (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z y).2
    (codimensionOneNormalIndex m) ≠ 0
  exact y.2.2

/-- The normal coordinate bundled as an actual holomorphic unit. -/
def codimensionOneNormalCoordinateUnit :
    (OpenHolomorphicFunctions X (m + 1)
      (.op (codimensionOnePuncturedNormalOpen X Y i m z)))ˣ where
  val := codimensionOneNormalCoordinateSection X Y i m z
  inv := ⟨fun y ↦ ((codimensionOneNormalCoordinateSection X Y i m z).1 y)⁻¹,
    (holomorphicFunctionSheaf_section_analytic X (m + 1)
      (codimensionOneNormalCoordinateSection X Y i m z)).inv₀
        (codimensionOneNormalCoordinateSection_ne_zero X Y i m z)⟩
  val_inv := by
    apply ContMDiffMap.ext
    intro y
    exact mul_inv_cancel₀ (codimensionOneNormalCoordinateSection_ne_zero X Y i m z y)
  inv_val := by
    apply ContMDiffMap.ext
    intro y
    exact inv_mul_cancel₀ (codimensionOneNormalCoordinateSection_ne_zero X Y i m z y)

/-! ### The positively oriented normal loop -/

/-- The standard positive unit circle in the one-dimensional normal space. -/
def codimensionOneNormalCircle (t : ℝ) : Fin ((m + 1) - m) → ℂ :=
  fun _ ↦ Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))

theorem codimensionOneNormalCircle_ne_zero (t : ℝ) :
    codimensionOneNormalCircle m t ≠ 0 := by
  intro h
  have hzero :
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) = 0 := by
    simpa only [codimensionOneNormalCircle, Pi.zero_apply] using
      congrFun h (codimensionOneNormalIndex m)
  exact Complex.exp_ne_zero _ hzero

theorem continuous_codimensionOneNormalCircle :
    Continuous (codimensionOneNormalCircle m) := by
  unfold codimensionOneNormalCircle
  apply continuous_pi
  intro j
  fun_prop

@[simp]
theorem codimensionOneNormalCircle_zero :
    codimensionOneNormalCircle m 0 = 1 := by
  ext j
  simp [codimensionOneNormalCircle]

@[simp]
theorem codimensionOneNormalCircle_one :
    codimensionOneNormalCircle m 1 = 1 := by
  ext j
  simp [codimensionOneNormalCircle, Complex.exp_two_pi_mul_I]

@[simp]
theorem norm_codimensionOneNormalCircle (t : ℝ) :
    ‖codimensionOneNormalCircle m t‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [codimensionOneNormalCircle, Complex.norm_exp]
    simp
  · have h := norm_le_pi_norm (codimensionOneNormalCircle m t)
      (codimensionOneNormalIndex m)
    calc
      1 = ‖Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))‖ := by
        rw [Complex.norm_exp]
        simp
      _ ≤ ‖codimensionOneNormalCircle m t‖ := by
        simpa only [codimensionOneNormalCircle] using h

/-- The radial compression of the positive normal circle into the selected
holomorphic flattening chart. -/
def codimensionOneNormalLoopPoint (t : ℝ) : ComplexPoint X :=
  (flattenedSupportHomeomorph (Fin m → ℂ) ((m + 1) - m)
    (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z)
    (Point.map i z)
    (closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z)
      (0, codimensionOneNormalCircle m t)).1

theorem codimensionOneNormalLoopPoint_mem_source (t : ℝ) :
    codimensionOneNormalLoopPoint X Y i m z t ∈
      (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z).source := by
  exact flattenedSupportNeighborhood_subset_source (Fin m → ℂ) ((m + 1) - m)
    (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z)
    (Point.map i z)
    (closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z)
    ((flattenedSupportHomeomorph (Fin m → ℂ) ((m + 1) - m)
      (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z)
      (Point.map i z)
      (closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z)
        (0, codimensionOneNormalCircle m t)).property)

theorem codimensionOneNormalLoopPoint_coordinate_ne_zero (t : ℝ) :
    codimensionOneNormalCoordinate X Y i m z
      (codimensionOneNormalLoopPoint X Y i m z t) ≠ 0 := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z
  let x := Point.map i z
  let hx := closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z
  intro hzero
  have hnormal : (e (codimensionOneNormalLoopPoint X Y i m z t)).2 = 0 := by
    ext j
    have hj : j = codimensionOneNormalIndex m := by
      apply Fin.ext
      dsimp [codimensionOneNormalIndex]
      omega
    subst j
    exact hzero
  have hcompressed :
      (OpenPartialHomeomorph.univBall (e x)
        (flattenedSupportRadius (Fin m → ℂ) ((m + 1) - m) e x hx)
          (0, codimensionOneNormalCircle m t)).2 = 0 := by
    rw [← flattenedSupportHomeomorph_coordinates (Fin m → ℂ)
      ((m + 1) - m) e x hx (0, codimensionOneNormalCircle m t)]
    exact hnormal
  have he : e x = ((e x).1, (0 : Fin ((m + 1) - m) → ℂ)) := by
    apply Prod.ext
    · rfl
    · dsimp [e, x]
      simp
  have hvzero : codimensionOneNormalCircle m t = 0 :=
    (univBall_normal_eq_zero_iff (Fin m → ℂ) ((m + 1) - m)
      (e x).1
      (flattenedSupportRadius (Fin m → ℂ) ((m + 1) - m) e x hx)
      (flattenedSupportRadius_pos (Fin m → ℂ) ((m + 1) - m) e x hx)
      (0, codimensionOneNormalCircle m t)).mp (by
        rw [← he]
        exact hcompressed)
  exact codimensionOneNormalCircle_ne_zero m t hvzero

/-- The actual one-turn loop, valued in the punctured normal chart. -/
def codimensionOneNormalLoop (t : ℝ) :
    codimensionOnePuncturedNormalOpen X Y i m z :=
  ⟨codimensionOneNormalLoopPoint X Y i m z t,
    codimensionOneNormalLoopPoint_mem_source X Y i m z t,
    codimensionOneNormalLoopPoint_coordinate_ne_zero X Y i m z t⟩

theorem continuous_codimensionOneNormalLoop :
    Continuous (codimensionOneNormalLoop X Y i m z) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ ↦
    ((flattenedSupportHomeomorph (Fin m → ℂ) ((m + 1) - m)
      (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z)
      (Point.map i z)
      (closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z))
        (0, codimensionOneNormalCircle m t)).1)
  simpa [Function.comp_def] using
    continuous_subtype_val.comp
      ((flattenedSupportHomeomorph (Fin m → ℂ) ((m + 1) - m)
        (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z)
        (Point.map i z)
        (closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z)).continuous.comp
          (continuous_const.prodMk (continuous_codimensionOneNormalCircle m)))

theorem codimensionOneNormalLoop_closed :
    codimensionOneNormalLoop X Y i m z 1 =
      codimensionOneNormalLoop X Y i m z 0 := by
  apply Subtype.ext
  simp [codimensionOneNormalLoop, codimensionOneNormalLoopPoint]

@[simp]
theorem norm_codimensionOneNormalLoopInput (t : ℝ) :
    ‖((0 : Fin m → ℂ), codimensionOneNormalCircle m t)‖ = 1 := by
  simp [Prod.norm_def, norm_codimensionOneNormalCircle]

/-- Along the radial normal loop, the holomorphic normal coordinate is a
positive real constant times the standard one-turn complex exponential. -/
theorem codimensionOneNormalCoordinate_normalLoop (t : ℝ) :
    codimensionOneNormalCoordinate X Y i m z
        (codimensionOneNormalLoopPoint X Y i m z t) =
      ((flattenedSupportRadius (Fin m → ℂ) ((m + 1) - m)
          (closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z)
          (Point.map i z)
          (closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z)) *
        (Real.sqrt 2)⁻¹) •
          Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m (m + 1) z
  let x := Point.map i z
  let hx := closedImmersionHolomorphicFlatteningChart_mem_source X Y i m (m + 1) z
  let r := flattenedSupportRadius (Fin m → ℂ) ((m + 1) - m) e x hx
  rw [codimensionOneNormalCoordinate_eq_flatteningChart]
  change (e ((flattenedSupportHomeomorph (Fin m → ℂ) ((m + 1) - m) e x hx)
      (0, codimensionOneNormalCircle m t)).1).2 (codimensionOneNormalIndex m) =
    (r * (Real.sqrt 2)⁻¹) •
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))
  rw [flattenedSupportHomeomorph_coordinates (Fin m → ℂ)
    ((m + 1) - m) e x hx (0, codimensionOneNormalCircle m t)]
  rw [OpenPartialHomeomorph.univBall, dif_pos
    (flattenedSupportRadius_pos (Fin m → ℂ) ((m + 1) - m) e x hx)]
  change (r • ((Real.sqrt (1 + ‖((0 : Fin m → ℂ),
    codimensionOneNormalCircle m t)‖ ^ 2))⁻¹ •
      ((0 : Fin m → ℂ), codimensionOneNormalCircle m t)) + e x).2
        (codimensionOneNormalIndex m) = _
  rw [norm_codimensionOneNormalLoopInput]
  dsimp [r, e, x, hx]
  simp [codimensionOneNormalCircle]
  ring_nf

/-- The actual holomorphic normal-coordinate unit makes exactly one positive
turn on the radial normal loop. -/
theorem codimensionOneNormalCoordinateUnit_one_turn (t : ℝ) :
    (codimensionOneNormalCoordinateUnit X Y i m z).val.1
        (codimensionOneNormalLoop X Y i m z t) =
      (codimensionOneNormalCoordinateUnit X Y i m z).val.1
          (codimensionOneNormalLoop X Y i m z 0) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
  change codimensionOneNormalCoordinate X Y i m z
      (codimensionOneNormalLoopPoint X Y i m z t) =
    codimensionOneNormalCoordinate X Y i m z
        (codimensionOneNormalLoopPoint X Y i m z 0) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))
  rw [codimensionOneNormalCoordinate_normalLoop X Y i m z t,
    codimensionOneNormalCoordinate_normalLoop X Y i m z 0]
  simp

/-- The punctured normal-coordinate unit has a nonzero, integrally normalized
exponential obstruction.  Its normalization is witnessed by one positive turn
around the normal slice. -/
theorem codimensionOneNormalCoordinateUnit_logarithmObstruction_ne_zero :
    holomorphicUnitLogarithmObstruction X (m + 1)
      (codimensionOnePuncturedNormalOpen X Y i m z)
      (codimensionOneNormalCoordinateUnit X Y i m z) ≠ 0 := by
  exact holomorphicUnitLogarithmObstruction_ne_zero_of_loop X (m + 1)
    (codimensionOnePuncturedNormalOpen X Y i m z)
    (codimensionOneNormalCoordinateUnit X Y i m z)
    (codimensionOneNormalLoop X Y i m z)
    (continuous_codimensionOneNormalLoop X Y i m z)
    (codimensionOneNormalLoop_closed X Y i m z)
    (codimensionOneNormalCoordinateUnit_one_turn X Y i m z)

end AlgebraicGeometry.ComplexPoint
