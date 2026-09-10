/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticBranchDivision
public import Other.AlgebraicGeometry.ExplicitEllipticGlobalHolomorphicConstancy

/-!
# Nonvanishing of the explicit elliptic curve Cech class

This file completes the CM pole argument for the adjusted two-chart
representative.  A hypothetical coboundary is first projected to the `-i`
eigenspace.  Its `Z`-chart term is divisible by `y`; after division the two
chart quotients glue to a global holomorphic function.  Compactness makes
that function constant along the explicit path from infinity, contradicting
the simple pole of the adjusted representative at infinity.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace MvPolynomial Topology
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pointwise evaluation of restriction for the holomorphic-function
presheaf. -/
@[simp] theorem holomorphicRestrictionAlgHom_apply_of_le
    {U V : Opens (TopCat.of (ComplexPoint curveVariety))} (h : V ≤ U)
    (f : OpenHolomorphicFunctions curveVariety 1 (.op U)) (z : V) :
    (holomorphicRestrictionAlgHom curveVariety 1 (homOfLE h).op f).1 z =
      f.1 ⟨z.1, h z.2⟩ := by
  rfl

/-- Pointwise form of restriction for analytic opens induced by regular
opens. -/
@[simp] theorem holomorphicRestrictionAlgHom_apply_regular
    {U V : curve.Opens} (h : V ≤ U)
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety U)))
    (z : regularAnalyticOpen curveVariety V) :
    (holomorphicRestrictionAlgHom curveVariety 1
      (regularAnalyticRestriction curveVariety h).op f).1 z =
        f.1 ⟨z.1, h z.2⟩ := by
  rfl

/-- Pointwise evaluation of a regular function regarded as holomorphic. -/
@[simp] theorem regularToHolomorphicAlgHom_apply
    (U : curve.Opens) (s : Γ(curve, U))
    (z : regularAnalyticOpen curveVariety U) :
    (regularToHolomorphicAlgHom curveVariety 1 U s).1 z =
      Point.evaluate U s z.1 := by
  rfl

/-- The affine coordinate `u = X/Y` on the `Y` chart. -/
def curveYAffineU : Γ(curve, curveYOpen) :=
  hypersurfaceCoordinateMap
    (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime) (X 0)

/-- The affine coordinate `v = Z/Y` on the `Y` chart. -/
def curveYAffineV : Γ(curve, curveYOpen) :=
  hypersurfaceCoordinateMap
    (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime) (X 1)

/-- The two `Y`-chart coordinates as holomorphic functions. -/
def curveYHolomorphicU : OpenHolomorphicFunctions curveVariety 1
    (.op (regularAnalyticOpen curveVariety curveYOpen)) :=
  regularToHolomorphicAlgHom curveVariety 1 curveYOpen curveYAffineU

def curveYHolomorphicV : OpenHolomorphicFunctions curveVariety 1
    (.op (regularAnalyticOpen curveVariety curveYOpen)) :=
  regularToHolomorphicAlgHom curveVariety 1 curveYOpen curveYAffineV

/-- The `Z`-chart coordinate `y = Y/Z` as a holomorphic function. -/
def curveZHolomorphicY : OpenHolomorphicFunctions curveVariety 1
    (.op (regularAnalyticOpen curveVariety curveZOpen)) :=
  regularToHolomorphicAlgHom curveVariety 1 curveZOpen
    curveZOverlapCoordinate

@[simp] theorem curveYAffineU_restrict_overlap :
    regularSectionRestriction curveVariety curveCMOverlap_le_y curveYAffineU =
      curveCMOverlapYU := by
  rfl

@[simp] theorem curveYAffineV_restrict_overlap :
    regularSectionRestriction curveVariety curveCMOverlap_le_y curveYAffineV =
      curveCMOverlapYV := by
  rfl

@[simp] theorem curveYHolomorphicU_restrict_overlap :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op
        curveYHolomorphicU =
      regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
        curveCMOverlapYU := by
  exact regularToHolomorphic_restrict curveVariety 1 curveCMOverlap_le_y _

@[simp] theorem curveYHolomorphicV_restrict_overlap :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op
        curveYHolomorphicV =
      regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
        curveCMOverlapYV := by
  exact regularToHolomorphic_restrict curveVariety 1 curveCMOverlap_le_y _

@[simp] theorem curveZHolomorphicY_restrict_overlap :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op
        curveZHolomorphicY =
      regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
        curveCMOverlapZY := by
  unfold curveZHolomorphicY curveCMOverlapZY
  rw [curveZOverlapCoordinate_eq_coordinate]
  exact regularToHolomorphic_restrict curveVariety 1 curveCMOverlap_le_z _

/-- The quotient expression on the `Y` chart forced by a projected
coboundary after dividing its `Z`-chart term by `y`. -/
def curveCechPoleQuotientY
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)) :=
  curveYHolomorphicU ^ 2 + curveYHolomorphicV ^ 2 +
    curveYHolomorphicV * fY

/-- The adjusted representative satisfies `v a = u² + v²` on the
overlap. -/
theorem curveCMOverlapYV_mul_adjusted :
    curveCMOverlapYV * curveCechAdjustedRegularRepresentative =
      curveCMOverlapYU ^ 2 + curveCMOverlapYV ^ 2 := by
  rw [curveCechAdjustedRegularRepresentative]
  have hy := curveCMOverlap_y_mul_v
  unfold curveCechRegularRepresentative
  calc
    curveCMOverlapYV *
        (curveCMOverlapZX ^ 2 * curveCMOverlapYV + curveCMOverlapYV) =
      (curveCMOverlapZX * curveCMOverlapYV) ^ 2 +
        curveCMOverlapYV ^ 2 := by ring
    _ = _ := by rw [curveCMOverlap_x_mul_v]

/-- Multiplying the adjusted representative by `u` removes its simple pole
and gives a function which takes value one at infinity. -/
theorem curveCMOverlapYU_mul_adjusted :
    curveCMOverlapYU * curveCechAdjustedRegularRepresentative =
      1 + 2 * curveCMOverlapYU * curveCMOverlapYV := by
  rw [curveCechAdjustedRegularRepresentative_eq]
  have hu : curveCMOverlapYU *
      (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) = 1 :=
    Units.mul_inv curveCMOverlapYUUnit
  calc
    curveCMOverlapYU *
        ((↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
          2 * curveCMOverlapYV) =
      curveCMOverlapYU *
          (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
        2 * curveCMOverlapYU * curveCMOverlapYV := by ring
    _ = _ := by rw [hu]

/-- Both affine coordinates of the `Y` chart vanish at infinity, stated with
the chart presentation used by the CM construction. -/
theorem evaluate_curveYAffineCoordinate_infinity (j : Fin 2) :
    Point.evaluate curveYOpen
        (hypersurfaceCoordinateMap
          (chartEquation (Equiv.swap (1 : Fin 3) 2))
          (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
            chartEquation_y_prime) (X j)) infinity = 0 := by
  by_contra h
  have hn := (evaluate_curveChartCoordinate_ne_zero_iff
    (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime j ![0, 1, 0]
    (by intro hP; have h1 := congrFun hP 1; simp at h1)
    (WeierstrassCurve.Projective.equation_zero) (by simp)).1 h
  fin_cases j <;> exact hn rfl

@[simp] theorem curveYHolomorphicU_infinity :
    curveYHolomorphicU.1 ⟨infinity, infinity_mem_chart_one⟩ = 0 := by
  change Point.evaluate curveYOpen curveYAffineU infinity = 0
  exact evaluate_curveYAffineCoordinate_infinity 0

@[simp] theorem curveYHolomorphicV_infinity :
  curveYHolomorphicV.1 ⟨infinity, infinity_mem_chart_one⟩ = 0 := by
  change Point.evaluate curveYOpen curveYAffineV infinity = 0
  exact evaluate_curveYAffineCoordinate_infinity 1

@[simp] theorem curveCechPoleQuotientY_infinity
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    (curveCechPoleQuotientY fY).1
      ⟨infinity, infinity_mem_chart_one⟩ = 0 := by
  change curveYHolomorphicU.1 ⟨infinity, infinity_mem_chart_one⟩ ^ 2 +
      curveYHolomorphicV.1 ⟨infinity, infinity_mem_chart_one⟩ ^ 2 +
        curveYHolomorphicV.1 ⟨infinity, infinity_mem_chart_one⟩ *
          fY.1 ⟨infinity, infinity_mem_chart_one⟩ = 0
  rw [curveYHolomorphicU_infinity, curveYHolomorphicV_infinity]
  ring

/-- The quotients obtained on the two charts agree on their overlap. -/
theorem curveCechPoleQuotients_compatible
    (fZ : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (qZ : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (hcob :
      holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op fZ -
        holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op fY =
        regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative)
    (hdiv : curveZHolomorphicY * qZ = fZ) :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op qZ =
      holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op
        (curveCechPoleQuotientY fY) := by
  let rZ := holomorphicRestrictionAlgHom curveVariety 1
    (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op
  let rY := holomorphicRestrictionAlgHom curveVariety 1
    (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op
  let η := regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
  have hy : η curveCMOverlapZY * η curveCMOverlapYV = 1 := by
    rw [← map_mul, curveCMOverlap_y_mul_v, map_one]
  have ha : η curveCMOverlapYV *
        η curveCechAdjustedRegularRepresentative =
      η curveCMOverlapYU ^ 2 + η curveCMOverlapYV ^ 2 := by
    rw [← map_mul, curveCMOverlapYV_mul_adjusted, map_add, map_pow, map_pow]
  have hd : η curveCMOverlapZY * rZ qZ = rZ fZ := by
    calc
      η curveCMOverlapZY * rZ qZ = rZ curveZHolomorphicY * rZ qZ := by
        rw [curveZHolomorphicY_restrict_overlap]
      _ = rZ (curveZHolomorphicY * qZ) := by rw [map_mul]
      _ = rZ fZ := by rw [hdiv]
  have hcob' : rZ fZ = η curveCechAdjustedRegularRepresentative + rY fY := by
    linear_combination hcob
  have hru : rY curveYHolomorphicU = η curveCMOverlapYU :=
    curveYHolomorphicU_restrict_overlap
  have hrv : rY curveYHolomorphicV = η curveCMOverlapYV :=
    curveYHolomorphicV_restrict_overlap
  unfold curveCechPoleQuotientY
  rw [map_add, map_add, map_pow, map_pow, map_mul, hru, hrv]
  calc
    rZ qZ = 1 * rZ qZ := by rw [one_mul]
    _ = (η curveCMOverlapYV * η curveCMOverlapZY) * rZ qZ := by
      rw [mul_comm _ (η curveCMOverlapZY), hy]
    _ = η curveCMOverlapYV *
        (η curveCMOverlapZY * rZ qZ) := by ring
    _ = η curveCMOverlapYV * rZ fZ := by rw [hd]
    _ = η curveCMOverlapYV *
        (η curveCechAdjustedRegularRepresentative + rY fY) := by rw [hcob']
    _ = (η curveCMOverlapYU ^ 2 + η curveCMOverlapYV ^ 2) +
        η curveCMOverlapYV * rY fY := by rw [mul_add, ha]
    _ = _ := by ring

/-- The compatible chart quotients glue to a global holomorphic function. -/
theorem exists_curveCechPoleGlobalQuotient
    (fZ : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (qZ : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (hcob :
      holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op fZ -
        holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op fY =
        regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative)
    (hdiv : curveZHolomorphicY * qZ = fZ) :
    ∃ q : OpenHolomorphicFunctions curveVariety 1 (.op ⊤),
      holomorphicRestrictionAlgHom curveVariety 1
          (homOfLE (show regularAnalyticOpen curveVariety curveZOpen ≤ ⊤
            from le_top)).op q = qZ ∧
        holomorphicRestrictionAlgHom curveVariety 1
          (homOfLE (show regularAnalyticOpen curveVariety curveYOpen ≤ ⊤
            from le_top)).op q = curveCechPoleQuotientY fY := by
  let U : Fin 2 → Opens (TopCat.of (ComplexPoint curveVariety)) :=
    ![regularAnalyticOpen curveVariety curveZOpen,
      regularAnalyticOpen curveVariety curveYOpen]
  let sf : ∀ i : Fin 2,
      OpenHolomorphicFunctions curveVariety 1 (.op (U i)) :=
    Fin.cases qZ
      (Fin.cases (curveCechPoleQuotientY fY) (fun i => i.elim0))
  have hcompat : TopCat.Presheaf.IsCompatible
      (holomorphicFunctionSheaf curveVariety 1).presheaf U sf := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · apply ContMDiffMap.ext
      intro z
      let z' : regularAnalyticOpen curveVariety curveCMOverlap :=
        ⟨z.1, by
          rw [curveCMOverlap_eq]
          exact z.2⟩
      exact congrArg (fun w => w.1 z')
        (curveCechPoleQuotients_compatible fZ fY qZ hcob hdiv)
    · apply ContMDiffMap.ext
      intro z
      let z' : regularAnalyticOpen curveVariety curveCMOverlap :=
        ⟨z.1, by
          rw [curveCMOverlap_eq]
          exact ⟨z.2.2, z.2.1⟩⟩
      exact congrArg (fun w => w.1 z')
        (curveCechPoleQuotients_compatible fZ fY qZ hcob hdiv).symm
    · rfl
  have hcover : (⊤ : Opens (TopCat.of (ComplexPoint curveVariety))) ≤ iSup U := by
    rw [← curveAnalyticOpen_cover]
    exact sup_le (le_iSup U 0) (le_iSup U 1)
  obtain ⟨q, hq, _⟩ :=
    (holomorphicFunctionSheaf curveVariety 1).existsUnique_gluing'
      U ⊤ (fun _ => homOfLE le_top) hcover sf hcompat
  exact ⟨q, hq 0, hq 1⟩

/-! ### The explicit approach to infinity through the overlap -/

/-- Every positive point of the explicit infinity path lies in the `Z`
chart. -/
theorem infinityToOnePath_mem_curveZOpen_of_pos
    (t : Set.Icc (0 : ℝ) 1) (ht : 0 < t.1) :
    (infinityToOnePath t).underlying ∈ curveZOpen := by
  change (curvePoint (infinityToOneVector t)
    (infinityToOneVector_ne_zero t) (infinityToOneVector_equation t)).underlying
      ∈ chart 2
  apply (curvePoint_mem_chart_iff _ _ _ 2).2
  have hreal : t.1 ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt ht)
  have hcomplex : ((t.1 ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
  simpa [infinityToOneVector] using hcomplex

/-- Before its other endpoint, the explicit infinity path lies in the `Y`
chart. -/
theorem infinityToOnePath_mem_curveYOpen_of_lt_one
    (t : Set.Icc (0 : ℝ) 1) (ht : t.1 < 1) :
    (infinityToOnePath t).underlying ∈ curveYOpen := by
  change (curvePoint (infinityToOneVector t)
    (infinityToOneVector_ne_zero t) (infinityToOneVector_equation t)).underlying
      ∈ chart 1
  apply (curvePoint_mem_chart_iff _ _ _ 1).2
  have hreal : Real.sqrt (1 - t.1 ^ 4) ≠ 0 := ne_of_gt <|
    Real.sqrt_pos.2
      (sub_pos.2 (pow_lt_one₀ t.2.1 ht (by norm_num : (4 : ℕ) ≠ 0)))
  have hcomplex : ((Real.sqrt (1 - t.1 ^ 4) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hreal
  simpa [infinityToOneVector] using hcomplex

/-- The first half of the path, with a domain on which the `Y`-chart lift is
defined everywhere. -/
abbrev curveInfinityHalfInterval := Set.Icc (0 : ℝ) (1 / 2)

def curveInfinityHalfToUnit (t : curveInfinityHalfInterval) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨t.1, t.2.1, t.2.2.trans (by norm_num)⟩

def curveInfinityHalfPath (t : curveInfinityHalfInterval) :
    ComplexPoint curveVariety :=
  infinityToOnePath (curveInfinityHalfToUnit t)

theorem curveInfinityHalfPath_mem_curveYOpen
    (t : curveInfinityHalfInterval) :
    (curveInfinityHalfPath t).underlying ∈ curveYOpen :=
  infinityToOnePath_mem_curveYOpen_of_lt_one _
    (t.2.2.trans_lt (by norm_num))

/-- The half-path lifted to the analytic `Y` chart. -/
def curveInfinityHalfPathY (t : curveInfinityHalfInterval) :
    regularAnalyticOpen curveVariety curveYOpen :=
  ⟨curveInfinityHalfPath t, curveInfinityHalfPath_mem_curveYOpen t⟩

theorem continuous_curveInfinityHalfToUnit :
    Continuous curveInfinityHalfToUnit :=
  continuous_subtype_val.subtype_mk _

theorem continuous_curveInfinityHalfPath :
    Continuous curveInfinityHalfPath :=
  continuous_infinityToOnePath.comp continuous_curveInfinityHalfToUnit

theorem continuous_curveInfinityHalfPathY :
    Continuous curveInfinityHalfPathY :=
  continuous_curveInfinityHalfPath.subtype_mk _

def curveInfinityHalfZero : curveInfinityHalfInterval :=
  ⟨0, by constructor <;> norm_num⟩

def curveInfinityHalfEnd : curveInfinityHalfInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem curveInfinityHalfPath_zero :
    curveInfinityHalfPath curveInfinityHalfZero = infinity := by
  calc
    curveInfinityHalfPath curveInfinityHalfZero =
        infinityToOnePath ⟨0, by constructor <;> norm_num⟩ := by
      apply congrArg infinityToOnePath
      apply Subtype.ext
      rfl
    _ = infinity := infinityToOnePath_zero

@[simp] theorem curveInfinityHalfPathY_zero :
    (curveInfinityHalfPathY curveInfinityHalfZero).1 = infinity := by
  exact curveInfinityHalfPath_zero

theorem curveInfinityHalfPathY_zero_eq :
    curveInfinityHalfPathY curveInfinityHalfZero =
      (⟨infinity, infinity_mem_chart_one⟩ :
        regularAnalyticOpen curveVariety curveYOpen) := by
  apply Subtype.ext
  exact curveInfinityHalfPath_zero

/-- Infinity is in the closure, inside the `Y` chart, of the positive half
of the explicit path. -/
theorem curveInfinityHalfPathY_zero_mem_closure :
    curveInfinityHalfPathY curveInfinityHalfZero ∈
      closure (curveInfinityHalfPathY ''
        Set.Ioc curveInfinityHalfZero curveInfinityHalfEnd) := by
  apply mem_closure_image continuous_curveInfinityHalfPathY.continuousAt
  rw [closure_Ioc]
  · exact ⟨le_rfl, by
      change (0 : ℝ) ≤ 1 / 2
      norm_num⟩
  · intro h
    have hv := congrArg Subtype.val h
    norm_num [curveInfinityHalfZero, curveInfinityHalfEnd] at hv

/-- Every point of the half-path lies in the connected component of
infinity. -/
theorem curveInfinityHalfPath_mem_connectedComponent_infinity
    (t : curveInfinityHalfInterval) :
    curveInfinityHalfPath t ∈ connectedComponent infinity := by
  have hc : IsConnected (Set.range infinityToOnePath) :=
    isConnected_range continuous_infinityToOnePath
  exact hc.subset_connectedComponent
    ⟨⟨0, by constructor <;> norm_num⟩, infinityToOnePath_zero⟩
    ⟨curveInfinityHalfToUnit t, rfl⟩

/-- A glued pole quotient vanishes at infinity because its `Y`-chart
formula does. -/
theorem curveCechPoleGlobalQuotient_infinity
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (q : OpenHolomorphicFunctions curveVariety 1 (.op ⊤))
    (hqY : holomorphicRestrictionAlgHom curveVariety 1
        (homOfLE (show regularAnalyticOpen curveVariety curveYOpen ≤ ⊤
          from le_top)).op q = curveCechPoleQuotientY fY) :
    q.1 (curvePointToTopOpen infinity) = 0 := by
  have h := congrArg
    (fun s : OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveYOpen)) =>
      s.1 ⟨infinity, infinity_mem_chart_one⟩) hqY
  change q.1 (curvePointToTopOpen infinity) =
    (curveCechPoleQuotientY fY).1
      ⟨infinity, infinity_mem_chart_one⟩ at h
  exact h.trans (curveCechPoleQuotientY_infinity fY)

/-- The global quotient therefore vanishes at every point of the explicit
half-path. -/
theorem curveCechPoleGlobalQuotient_halfPath
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (q : OpenHolomorphicFunctions curveVariety 1 (.op ⊤))
    (hqY : holomorphicRestrictionAlgHom curveVariety 1
        (homOfLE (show regularAnalyticOpen curveVariety curveYOpen ≤ ⊤
          from le_top)).op q = curveCechPoleQuotientY fY)
    (t : curveInfinityHalfInterval) :
    q.1 (curvePointToTopOpen (curveInfinityHalfPath t)) = 0 := by
  calc
    q.1 (curvePointToTopOpen (curveInfinityHalfPath t)) =
        q.1 (curvePointToTopOpen infinity) :=
      curveGlobalHolomorphicFunction_eq_of_mem_connectedComponent q
        (curvePointToTopOpen infinity)
        (curvePointToTopOpen (curveInfinityHalfPath t))
        (continuous_curvePointToTopOpen.mapsTo_connectedComponent infinity
          (curveInfinityHalfPath_mem_connectedComponent_infinity t))
    _ = 0 := curveCechPoleGlobalQuotient_infinity fY q hqY

/-- The holomorphic left-hand side obtained after clearing the adjusted
representative's pole. -/
def curveCechPoleEquationLeft
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)) :=
  curveYHolomorphicU * fY

/-- The regular right-hand side of the pole-cleared coboundary equation. -/
def curveCechPoleEquationRight :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)) :=
  -(1 + 2 * curveYHolomorphicU * curveYHolomorphicV)

@[simp] theorem curveCechPoleEquationLeft_apply
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (z : regularAnalyticOpen curveVariety curveYOpen) :
    (curveCechPoleEquationLeft fY).1 z =
      curveYHolomorphicU.1 z * fY.1 z := by
  rfl

@[simp] theorem curveCechPoleEquationRight_apply
    (z : regularAnalyticOpen curveVariety curveYOpen) :
    curveCechPoleEquationRight.1 z =
      -(1 + 2 * curveYHolomorphicU.1 z * curveYHolomorphicV.1 z) := by
  unfold curveCechPoleEquationRight
  change (ContMDiffMap.evalRingHom z)
      (-(1 + 2 * curveYHolomorphicU * curveYHolomorphicV)) = _
  simp only [map_neg, map_add, map_one, map_mul, map_ofNat]
  have hu : (ContMDiffMap.evalRingHom z) curveYHolomorphicU =
      curveYHolomorphicU.1 z := rfl
  have hv : (ContMDiffMap.evalRingHom z) curveYHolomorphicV =
      curveYHolomorphicV.1 z := rfl
  rw [hu, hv]

/-- Along the positive half of the explicit path, a hypothetical projected
coboundary forces the pole-cleared equation `u fY = -(1+2uv)`. -/
theorem curveCechPoleEquation_on_halfPath
    (fZ : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (qZ : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (q : OpenHolomorphicFunctions curveVariety 1 (.op ⊤))
    (hcob :
      holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op fZ -
        holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op fY =
        regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative)
    (hdiv : curveZHolomorphicY * qZ = fZ)
    (hqZ : holomorphicRestrictionAlgHom curveVariety 1
        (homOfLE (show regularAnalyticOpen curveVariety curveZOpen ≤ ⊤
          from le_top)).op q = qZ)
    (hqY : holomorphicRestrictionAlgHom curveVariety 1
        (homOfLE (show regularAnalyticOpen curveVariety curveYOpen ≤ ⊤
          from le_top)).op q = curveCechPoleQuotientY fY)
    (t : curveInfinityHalfInterval)
    (ht : t ∈ Set.Ioc curveInfinityHalfZero curveInfinityHalfEnd) :
    (curveCechPoleEquationLeft fY).1 (curveInfinityHalfPathY t) =
      curveCechPoleEquationRight.1 (curveInfinityHalfPathY t) := by
  have htpos : 0 < t.1 := by
    change curveInfinityHalfZero.1 < t.1
    exact ht.1
  let p : ComplexPoint curveVariety := curveInfinityHalfPath t
  have hpZ : p.underlying ∈ curveZOpen :=
    infinityToOnePath_mem_curveZOpen_of_pos _ htpos
  have hpY : p.underlying ∈ curveYOpen :=
    curveInfinityHalfPath_mem_curveYOpen t
  let zZ : regularAnalyticOpen curveVariety curveZOpen := ⟨p, hpZ⟩
  let zY : regularAnalyticOpen curveVariety curveYOpen := ⟨p, hpY⟩
  let zO : regularAnalyticOpen curveVariety curveCMOverlap :=
    ⟨p, by
      rw [curveCMOverlap_eq]
      exact ⟨hpZ, hpY⟩⟩
  have hqZeval := congrArg
    (fun s : OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveZOpen)) => s.1 zZ) hqZ
  have hqZzero : qZ.1 zZ = 0 := by
    rw [← hqZeval]
    exact curveCechPoleGlobalQuotient_halfPath fY q hqY t
  have hfZzero : fZ.1 zZ = 0 := by
    have hd := congrArg
      (fun s : OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveZOpen)) => s.1 zZ) hdiv
    change curveZHolomorphicY.1 zZ * qZ.1 zZ = fZ.1 zZ at hd
    rw [hqZzero, mul_zero] at hd
    exact hd.symm
  have hc := congrArg
    (fun s : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)) => s.1 zO) hcob
  change fZ.1 zZ - fY.1 zY =
    Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative p at hc
  rw [hfZzero, zero_sub] at hc
  let ev := Point.evaluationHom (X := curveVariety) curveCMOverlap zO
  have ha := congrArg (fun s : Γ(curve, curveCMOverlap) => ev s)
    curveCMOverlapYU_mul_adjusted
  simp only [map_mul, map_add, map_one, map_ofNat] at ha
  dsimp only [ev] at ha
  rw [Point.evaluationHom_apply, Point.evaluationHom_apply,
    Point.evaluationHom_apply] at ha
  change Point.evaluate curveCMOverlap curveCMOverlapYU p *
      Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative p =
    1 + 2 * Point.evaluate curveCMOverlap curveCMOverlapYU p *
      Point.evaluate curveCMOverlap curveCMOverlapYV p at ha
  have hu0 := congrArg
    (fun s : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)) => s.1 zO)
    curveYHolomorphicU_restrict_overlap
  have hv0 := congrArg
    (fun s : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)) => s.1 zO)
    curveYHolomorphicV_restrict_overlap
  rw [holomorphicRestrictionAlgHom_apply_regular,
    regularToHolomorphicAlgHom_apply] at hu0 hv0
  have hu : curveYHolomorphicU.1 zY =
      Point.evaluate curveCMOverlap curveCMOverlapYU p := by
    simpa only [zY, zO] using hu0
  have hv : curveYHolomorphicV.1 zY =
      Point.evaluate curveCMOverlap curveCMOverlapYV p := by
    simpa only [zY, zO] using hv0
  have hfy : fY.1 zY =
      -Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative p := by
    linear_combination -hc
  have hscalar : curveYHolomorphicU.1 zY * fY.1 zY =
      -(1 + 2 * curveYHolomorphicU.1 zY * curveYHolomorphicV.1 zY) := by
    rw [hu, hv, hfy]
    linear_combination -ha
  have hzY : curveInfinityHalfPathY t = zY := by
    apply Subtype.ext
    rfl
  rw [hzY]
  rw [curveCechPoleEquationLeft_apply, curveCechPoleEquationRight_apply]
  exact hscalar

/-- The adjusted regular representative is not the difference of
holomorphic functions from the two affine charts. -/
theorem curveCechAdjustedRegularRepresentative_not_coboundary :
    ¬ ∃
      (fZ : OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveZOpen)))
      (fY : OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveYOpen))),
      holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op fZ -
        holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op fY =
        regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative := by
  rintro ⟨fZ₀, fY₀, hcob₀⟩
  obtain ⟨hcob, hfZ, hfY⟩ :=
    curveCechAdjustedCoboundary_project_to_cm_minus fZ₀ fY₀ hcob₀
  let fZ := curveZHolomorphicCMMinusPart fZ₀
  let fY := curveYHolomorphicCMMinusPart fY₀
  obtain ⟨qZ, hdiv⟩ :=
    exists_curveZHolomorphicCMMinusEigen_eq_overlapCoordinate_mul fZ hfZ
  change curveZHolomorphicY * qZ = fZ at hdiv
  obtain ⟨q, hqZ, hqY⟩ :=
    exists_curveCechPoleGlobalQuotient fZ fY qZ hcob hdiv
  have heq : Set.EqOn
      (curveCechPoleEquationLeft fY).1
      curveCechPoleEquationRight.1
      (curveInfinityHalfPathY ''
        Set.Ioc curveInfinityHalfZero curveInfinityHalfEnd) := by
    rintro z ⟨t, ht, rfl⟩
    exact curveCechPoleEquation_on_halfPath fZ fY qZ q hcob hdiv
      hqZ hqY t ht
  have heqInfinity := heq.closure
    (holomorphicFunctionSheaf_section_analytic curveVariety 1
      (curveCechPoleEquationLeft fY)).continuous
    (holomorphicFunctionSheaf_section_analytic curveVariety 1
      curveCechPoleEquationRight).continuous
    curveInfinityHalfPathY_zero_mem_closure
  rw [curveInfinityHalfPathY_zero_eq,
    curveCechPoleEquationLeft_apply,
    curveCechPoleEquationRight_apply,
    curveYHolomorphicU_infinity,
    curveYHolomorphicV_infinity] at heqInfinity
  norm_num at heqInfinity

/-- The actual analytic overlap representative is not a two-chart
coboundary. -/
theorem curveCechAdjustedHolomorphicRepresentative_not_coboundary :
    ¬ ∃
      (fZ : OpenHolomorphicFunctions curveVariety 1
        (.op (curveCechOpen 0)))
      (fY : OpenHolomorphicFunctions curveVariety 1
        (.op (curveCechOpen 1))),
      curveCechCoboundary fZ fY =
        curveCechAdjustedHolomorphicRepresentative := by
  rintro ⟨fZ, fY, h⟩
  apply curveCechAdjustedRegularRepresentative_not_coboundary
  refine ⟨fZ, fY, ?_⟩
  apply Subtype.ext
  funext z
  let z' : curveCechOverlap :=
    ⟨z.1, by
      rw [← regularAnalyticOpen_curveCMOverlap]
      exact z.2⟩
  have hz := congrArg (fun s => s.1 z') h
  change
    fZ.1 ⟨z.1, curveCMOverlap_le_z z.2⟩ -
        fY.1 ⟨z.1, curveCMOverlap_le_y z.2⟩ =
      Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative z.1
  change
    fZ.1 ⟨z'.1, z'.2.1⟩ -
        fY.1 ⟨z'.1, z'.2.2⟩ =
      curveCechAdjustedHolomorphicRepresentative.1 z' at hz
  have hrep : curveCechAdjustedHolomorphicRepresentative.1 z' =
      Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative z'.1 := by
    rw [curveCechAdjustedHolomorphicRepresentative,
      curveCechOpenFunctionAddEquiv,
      openHolomorphicFunctionAddEquivOfEq_apply,
      regularToHolomorphicAlgHom_apply]
  rw [hrep] at hz
  exact hz

/-- The explicit adjusted representative defines a nonzero degree-one
extension of the analytic structure sheaf. -/
theorem curveAdjustedHolomorphicCechClass_ne_zero :
    curveHolomorphicCechClass curveCechAdjustedHolomorphicRepresentative ≠ 0 := by
  intro hzero
  obtain ⟨fZ, fY, h⟩ :=
    (analyticTransitionExtClass_eq_zero_iff curveVariety
      (holomorphicAdditiveFunctionSheaf curveVariety 1)
      (curveCechOpen 0) (curveCechOpen 1) curveCechOpen_cover
      curveCechAdjustedHolomorphicRepresentative).mp hzero
  exact curveCechAdjustedHolomorphicRepresentative_not_coboundary
    ⟨fZ, fY, h⟩

end AlgebraicGeometry.ExplicitEllipticCandidate
