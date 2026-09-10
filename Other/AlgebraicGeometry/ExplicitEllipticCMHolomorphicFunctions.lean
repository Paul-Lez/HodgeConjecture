/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMTopology
public import Other.AlgebraicGeometry.HolomorphicFunctionPullback
public import Other.AlgebraicGeometry.CycleComponentLocalOrientation
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechProduct

/-!
# Complex multiplication on elliptic-curve holomorphic functions

The global order-four automorphism preserves both affine opens in the standard
two-chart cover.  We package its pullback as an algebra endomorphism of the
actual analytic holomorphic functions on either chart.  These are the
endomorphisms used to project a hypothetical Cech coboundary to its `-i`
eigenspace.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

/-- The affine Z-chart CM automorphism as a morphism over `Spec ℂ`. -/
def curveZOpenVarietyCMEnd :
    openScheme curveVariety curveZOpen ⟶
      openScheme curveVariety curveZOpen :=
  Over.homMk curveZCMChartIso.hom curveZCMChartIso_toBase

/-- The affine Y-chart CM automorphism as a morphism over `Spec ℂ`. -/
def curveYOpenVarietyCMEnd :
    openScheme curveVariety curveYOpen ⟶
      openScheme curveVariety curveYOpen :=
  Over.homMk curveYCMChartIso.hom curveYCMChartIso_toBase

@[reassoc]
theorem curveZOpenInclusion_curveVarietyCMEnd :
    openInclusion curveVariety curveZOpen ≫ curveVarietyCMEnd =
      curveZOpenVarietyCMEnd ≫ openInclusion curveVariety curveZOpen := by
  apply Over.OverMorphism.ext
  exact curveZOpen_ι_curveCMEnd

@[reassoc]
theorem curveYOpenInclusion_curveVarietyCMEnd :
    openInclusion curveVariety curveYOpen ≫ curveVarietyCMEnd =
      curveYOpenVarietyCMEnd ≫ openInclusion curveVariety curveYOpen := by
  apply Over.OverMorphism.ext
  exact curveYOpen_ι_curveCMEnd

/-- Complex multiplication maps the Z chart into itself. -/
theorem curveVarietyCMEnd_mem_curveZOpen
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen) :
    Point.map curveVarietyCMEnd z ∈ Point.overOpen curveZOpen := by
  let w := asOpenPoint curveVariety curveZOpen z hz
  have hw : Point.map (openInclusion curveVariety curveZOpen) w = z :=
    Over.OverMorphism.ext (liftToOpen_fac curveVariety curveZOpen z hz)
  have heq :
      Point.map curveVarietyCMEnd z =
        Point.map (openInclusion curveVariety curveZOpen)
          (Point.map curveZOpenVarietyCMEnd w) := by
    calc
      Point.map curveVarietyCMEnd z =
          Point.map curveVarietyCMEnd
            (Point.map (openInclusion curveVariety curveZOpen) w) := by rw [hw]
      _ = Point.map
          (openInclusion curveVariety curveZOpen ≫ curveVarietyCMEnd) w := by
            rw [Point.map_comp_apply]
      _ = Point.map
          (curveZOpenVarietyCMEnd ≫
            openInclusion curveVariety curveZOpen) w := by
              rw [curveZOpenInclusion_curveVarietyCMEnd]
      _ = Point.map (openInclusion curveVariety curveZOpen)
          (Point.map curveZOpenVarietyCMEnd w) := by
            rw [Point.map_comp_apply]
  rw [heq]
  change
    (Point.map (openInclusion curveVariety curveZOpen)
      (Point.map curveZOpenVarietyCMEnd w)).underlying ∈ curveZOpen
  rw [Point.underlying_map]
  exact (Point.map curveZOpenVarietyCMEnd w).underlying.property

/-- Complex multiplication maps the Y chart into itself. -/
theorem curveVarietyCMEnd_mem_curveYOpen
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveYOpen) :
    Point.map curveVarietyCMEnd z ∈ Point.overOpen curveYOpen := by
  let w := asOpenPoint curveVariety curveYOpen z hz
  have hw : Point.map (openInclusion curveVariety curveYOpen) w = z :=
    Over.OverMorphism.ext (liftToOpen_fac curveVariety curveYOpen z hz)
  have heq :
      Point.map curveVarietyCMEnd z =
        Point.map (openInclusion curveVariety curveYOpen)
          (Point.map curveYOpenVarietyCMEnd w) := by
    calc
      Point.map curveVarietyCMEnd z =
          Point.map curveVarietyCMEnd
            (Point.map (openInclusion curveVariety curveYOpen) w) := by rw [hw]
      _ = Point.map
          (openInclusion curveVariety curveYOpen ≫ curveVarietyCMEnd) w := by
            rw [Point.map_comp_apply]
      _ = Point.map
          (curveYOpenVarietyCMEnd ≫
            openInclusion curveVariety curveYOpen) w := by
              rw [curveYOpenInclusion_curveVarietyCMEnd]
      _ = Point.map (openInclusion curveVariety curveYOpen)
          (Point.map curveYOpenVarietyCMEnd w) := by
            rw [Point.map_comp_apply]
  rw [heq]
  change
    (Point.map (openInclusion curveVariety curveYOpen)
      (Point.map curveYOpenVarietyCMEnd w)).underlying ∈ curveYOpen
  rw [Point.underlying_map]
  exact (Point.map curveYOpenVarietyCMEnd w).underlying.property

/-- The fourth iterate acts trivially on complex points. -/
theorem curveVarietyCMEnd_four_apply (z : ComplexPoint curveVariety) :
    Point.map curveVarietyCMEnd
        (Point.map curveVarietyCMEnd
          (Point.map curveVarietyCMEnd
            (Point.map curveVarietyCMEnd z))) = z := by
  rw [← Point.map_comp_apply, ← Point.map_comp_apply,
    ← Point.map_comp_apply, curveVarietyCMEnd_four, Point.map_id]

/-- Membership in the Z chart is invariant under complex multiplication. -/
theorem curveVarietyCMEnd_mem_curveZOpen_iff (z : ComplexPoint curveVariety) :
    Point.map curveVarietyCMEnd z ∈ Point.overOpen curveZOpen ↔
      z ∈ Point.overOpen curveZOpen := by
  constructor
  · intro hz
    have h₁ := curveVarietyCMEnd_mem_curveZOpen _ hz
    have h₂ := curveVarietyCMEnd_mem_curveZOpen _ h₁
    have h₃ := curveVarietyCMEnd_mem_curveZOpen _ h₂
    rwa [curveVarietyCMEnd_four_apply] at h₃
  · exact curveVarietyCMEnd_mem_curveZOpen z

/-- Membership in the Y chart is invariant under complex multiplication. -/
theorem curveVarietyCMEnd_mem_curveYOpen_iff (z : ComplexPoint curveVariety) :
    Point.map curveVarietyCMEnd z ∈ Point.overOpen curveYOpen ↔
      z ∈ Point.overOpen curveYOpen := by
  constructor
  · intro hz
    have h₁ := curveVarietyCMEnd_mem_curveYOpen _ hz
    have h₂ := curveVarietyCMEnd_mem_curveYOpen _ h₁
    have h₃ := curveVarietyCMEnd_mem_curveYOpen _ h₂
    rwa [curveVarietyCMEnd_four_apply] at h₃
  · exact curveVarietyCMEnd_mem_curveYOpen z

/-- The inverse image of the Z analytic chart under CM is itself. -/
theorem curveVarietyCMEnd_comap_curveZOpen :
    (regularAnalyticOpen curveVariety curveZOpen).comap
        (analyticMapContinuous curveVariety curveVariety curveVarietyCMEnd) =
      regularAnalyticOpen curveVariety curveZOpen := by
  ext z
  exact curveVarietyCMEnd_mem_curveZOpen_iff z

/-- The inverse image of the Y analytic chart under CM is itself. -/
theorem curveVarietyCMEnd_comap_curveYOpen :
    (regularAnalyticOpen curveVariety curveYOpen).comap
        (analyticMapContinuous curveVariety curveVariety curveVarietyCMEnd) =
      regularAnalyticOpen curveVariety curveYOpen := by
  ext z
  exact curveVarietyCMEnd_mem_curveYOpen_iff z

/-! ### Pullback on the analytic chart rings -/

/-- The analytic CM self-map restricted to the Z chart. -/
def curveZAnalyticCMMap :
    regularAnalyticOpen curveVariety curveZOpen →
      regularAnalyticOpen curveVariety curveZOpen :=
  fun z ↦ ⟨Point.map curveVarietyCMEnd z.1,
    curveVarietyCMEnd_mem_curveZOpen z.1 z.2⟩

/-- The analytic CM self-map restricted to the Y chart. -/
def curveYAnalyticCMMap :
    regularAnalyticOpen curveVariety curveYOpen →
      regularAnalyticOpen curveVariety curveYOpen :=
  fun z ↦ ⟨Point.map curveVarietyCMEnd z.1,
    curveVarietyCMEnd_mem_curveYOpen z.1 z.2⟩

theorem contMDiff_curveZAnalyticCMMap :
    ContMDiff (modelWithCornersSelf ℂ (Fin 1 → ℂ))
      (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω curveZAnalyticCMMap := by
  intro x
  change ChartedSpace.LiftPropWithinAt
    (ContDiffWithinAtProp
      (modelWithCornersSelf ℂ (Fin 1 → ℂ))
      (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω)
    _ Set.univ x
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp
      (modelWithCornersSelf ℂ (Fin 1 → ℂ))
      (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω) _ Set.univ x).mp
  have h := ((contMDiff_analyticMap curveVariety curveVariety
    curveVarietyCMEnd 1 1).comp contMDiff_subtype_val) x
  have hfun : Subtype.val ∘ curveZAnalyticCMMap =
      Point.map curveVarietyCMEnd ∘ Subtype.val := by rfl
  rw [hfun]
  exact h

theorem contMDiff_curveYAnalyticCMMap :
    ContMDiff (modelWithCornersSelf ℂ (Fin 1 → ℂ))
      (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω curveYAnalyticCMMap := by
  intro x
  change ChartedSpace.LiftPropWithinAt
    (ContDiffWithinAtProp
      (modelWithCornersSelf ℂ (Fin 1 → ℂ))
      (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω)
    _ Set.univ x
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp
      (modelWithCornersSelf ℂ (Fin 1 → ℂ))
      (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω) _ Set.univ x).mp
  have h := ((contMDiff_analyticMap curveVariety curveVariety
    curveVarietyCMEnd 1 1).comp contMDiff_subtype_val) x
  have hfun : Subtype.val ∘ curveYAnalyticCMMap =
      Point.map curveVarietyCMEnd ∘ Subtype.val := by rfl
  rw [hfun]
  exact h

/-- Pullback by CM on the actual holomorphic functions of the Z chart. -/
def curveZHolomorphicCMEnd :
    OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveZOpen)) →ₐ[ℂ]
      OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveZOpen)) where
  toFun f := ⟨f.1 ∘ curveZAnalyticCMMap,
    ContMDiff.comp f.2 contMDiff_curveZAnalyticCMMap⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Pullback by CM on the actual holomorphic functions of the Y chart. -/
def curveYHolomorphicCMEnd :
    OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveYOpen)) →ₐ[ℂ]
      OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveYOpen)) where
  toFun f := ⟨f.1 ∘ curveYAnalyticCMMap,
    ContMDiff.comp f.2 contMDiff_curveYAnalyticCMMap⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem curveZHolomorphicCMEnd_apply
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (z : regularAnalyticOpen curveVariety curveZOpen) :
    (curveZHolomorphicCMEnd f).1 z =
      f.1 ⟨Point.map curveVarietyCMEnd z.1,
        curveVarietyCMEnd_mem_curveZOpen z.1 z.2⟩ := by
  rfl

@[simp]
theorem curveYHolomorphicCMEnd_apply
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (z : regularAnalyticOpen curveVariety curveYOpen) :
    (curveYHolomorphicCMEnd f).1 z =
      f.1 ⟨Point.map curveVarietyCMEnd z.1,
        curveVarietyCMEnd_mem_curveYOpen z.1 z.2⟩ := by
  rfl

/-- Four iterations of the restricted analytic CM map on the Z chart are the
identity. -/
theorem curveZAnalyticCMMap_four
    (z : regularAnalyticOpen curveVariety curveZOpen) :
    curveZAnalyticCMMap
        (curveZAnalyticCMMap
          (curveZAnalyticCMMap (curveZAnalyticCMMap z))) = z := by
  apply Subtype.ext
  exact curveVarietyCMEnd_four_apply z.1

/-- Four iterations of the restricted analytic CM map on the Y chart are the
identity. -/
theorem curveYAnalyticCMMap_four
    (z : regularAnalyticOpen curveVariety curveYOpen) :
    curveYAnalyticCMMap
        (curveYAnalyticCMMap
          (curveYAnalyticCMMap (curveYAnalyticCMMap z))) = z := by
  apply Subtype.ext
  exact curveVarietyCMEnd_four_apply z.1

/-- Pullback on Z-chart holomorphic functions has order dividing four. -/
theorem curveZHolomorphicCMEnd_four
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen))) :
    curveZHolomorphicCMEnd
        (curveZHolomorphicCMEnd
          (curveZHolomorphicCMEnd (curveZHolomorphicCMEnd f))) = f := by
  apply ContMDiffMap.ext
  intro z
  exact congrArg f.1 (curveZAnalyticCMMap_four z)

/-- Pullback on Y-chart holomorphic functions has order dividing four. -/
theorem curveYHolomorphicCMEnd_four
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    curveYHolomorphicCMEnd
        (curveYHolomorphicCMEnd
          (curveYHolomorphicCMEnd (curveYHolomorphicCMEnd f))) = f := by
  apply ContMDiffMap.ext
  intro z
  exact congrArg f.1 (curveYAnalyticCMMap_four z)

/-- The spectral projection of a Z-chart holomorphic function to the `-i`
eigenspace of CM. -/
def curveZHolomorphicCMMinusPart
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen))) :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)) :=
  (1 / 4 : ℂ) • (f + Complex.I • curveZHolomorphicCMEnd f -
    curveZHolomorphicCMEnd (curveZHolomorphicCMEnd f) -
    Complex.I • curveZHolomorphicCMEnd
      (curveZHolomorphicCMEnd (curveZHolomorphicCMEnd f)))

/-- The spectral projection of a Y-chart holomorphic function to the `-i`
eigenspace of CM. -/
def curveYHolomorphicCMMinusPart
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)) :=
  (1 / 4 : ℂ) • (f + Complex.I • curveYHolomorphicCMEnd f -
    curveYHolomorphicCMEnd (curveYHolomorphicCMEnd f) -
    Complex.I • curveYHolomorphicCMEnd
      (curveYHolomorphicCMEnd (curveYHolomorphicCMEnd f)))

/-- The projected Z-chart function has CM eigenvalue `-i`. -/
theorem curveZHolomorphicCMEnd_minusPart
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen))) :
    curveZHolomorphicCMEnd (curveZHolomorphicCMMinusPart f) =
      -Complex.I • curveZHolomorphicCMMinusPart f := by
  rw [curveZHolomorphicCMMinusPart, map_smul, map_sub, map_sub,
    map_add, map_smul, map_smul, curveZHolomorphicCMEnd_four]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- The projected Y-chart function has CM eigenvalue `-i`. -/
theorem curveYHolomorphicCMEnd_minusPart
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    curveYHolomorphicCMEnd (curveYHolomorphicCMMinusPart f) =
      -Complex.I • curveYHolomorphicCMMinusPart f := by
  rw [curveYHolomorphicCMMinusPart, map_smul, map_sub, map_sub,
    map_add, map_smul, map_smul, curveYHolomorphicCMEnd_four]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- A `-i` CM eigenfunction is fixed by the four-term `-i` projector. -/
theorem curveZHolomorphicCMMinusPart_eq_self
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (hf : curveZHolomorphicCMEnd f = -Complex.I • f) :
    curveZHolomorphicCMMinusPart f = f := by
  have h2 : curveZHolomorphicCMEnd (curveZHolomorphicCMEnd f) =
      (-Complex.I * -Complex.I) • f := by
    calc
      curveZHolomorphicCMEnd (curveZHolomorphicCMEnd f) =
          curveZHolomorphicCMEnd (-Complex.I • f) := congrArg _ hf
      _ = -Complex.I • curveZHolomorphicCMEnd f := map_smul _ _ _
      _ = -Complex.I • (-Complex.I • f) := by rw [hf]
      _ = (-Complex.I * -Complex.I) • f := by rw [smul_smul]
  have h3 : curveZHolomorphicCMEnd
        (curveZHolomorphicCMEnd (curveZHolomorphicCMEnd f)) =
      (-Complex.I * (-Complex.I * -Complex.I)) • f := by
    calc
      curveZHolomorphicCMEnd
          (curveZHolomorphicCMEnd (curveZHolomorphicCMEnd f)) =
        curveZHolomorphicCMEnd ((-Complex.I * -Complex.I) • f) :=
          congrArg _ h2
      _ = (-Complex.I * -Complex.I) • curveZHolomorphicCMEnd f :=
        map_smul _ _ _
      _ = (-Complex.I * -Complex.I) • (-Complex.I • f) := by rw [hf]
      _ = (-Complex.I * (-Complex.I * -Complex.I)) • f := by
        rw [smul_smul]
        congr 1
        ring
  rw [curveZHolomorphicCMMinusPart, h3, h2, hf]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- A `-i` CM eigenfunction is fixed by the four-term `-i` projector. -/
theorem curveYHolomorphicCMMinusPart_eq_self
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (hf : curveYHolomorphicCMEnd f = -Complex.I • f) :
    curveYHolomorphicCMMinusPart f = f := by
  have h2 : curveYHolomorphicCMEnd (curveYHolomorphicCMEnd f) =
      (-Complex.I * -Complex.I) • f := by
    calc
      curveYHolomorphicCMEnd (curveYHolomorphicCMEnd f) =
          curveYHolomorphicCMEnd (-Complex.I • f) := congrArg _ hf
      _ = -Complex.I • curveYHolomorphicCMEnd f := map_smul _ _ _
      _ = -Complex.I • (-Complex.I • f) := by rw [hf]
      _ = (-Complex.I * -Complex.I) • f := by rw [smul_smul]
  have h3 : curveYHolomorphicCMEnd
        (curveYHolomorphicCMEnd (curveYHolomorphicCMEnd f)) =
      (-Complex.I * (-Complex.I * -Complex.I)) • f := by
    calc
      curveYHolomorphicCMEnd
          (curveYHolomorphicCMEnd (curveYHolomorphicCMEnd f)) =
        curveYHolomorphicCMEnd ((-Complex.I * -Complex.I) • f) :=
          congrArg _ h2
      _ = (-Complex.I * -Complex.I) • curveYHolomorphicCMEnd f :=
        map_smul _ _ _
      _ = (-Complex.I * -Complex.I) • (-Complex.I • f) := by rw [hf]
      _ = (-Complex.I * (-Complex.I * -Complex.I)) • f := by
        rw [smul_smul]
        congr 1
        ring
  rw [curveYHolomorphicCMMinusPart, h3, h2, hf]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

end AlgebraicGeometry.ExplicitEllipticCandidate
