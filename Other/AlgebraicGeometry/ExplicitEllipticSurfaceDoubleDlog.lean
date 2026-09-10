/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceTopFormCech
public import Other.AlgebraicGeometry.AnalyticIteratedTransitionTwo
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceInfinity
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCotangentGeneration

/-!
# The elliptic-surface Cech product as a double logarithmic form

This file identifies the product of the adjusted elliptic-curve Cech representatives,
after multiplication by the explicit global holomorphic two-form, with the logarithmic
two-form of the two pulled transition units on the deepest product overlap.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

@[expose] noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

attribute [local instance] regularSectionAlgebra

local instance surfaceDoubleDlogAlgebra (V : surface.Opens) :
    Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

theorem curveYOpen_eq_chart : curveYOpen = chart 1 := by
  rfl

theorem regularAnalyticOpen_preimage
    {X Y : Over (Spec (.of ℂ))} (f : X ⟶ Y) (U : Y.left.Opens) :
    regularAnalyticOpen X (f.left ⁻¹ᵁ U) =
      (regularAnalyticOpen Y U).comap (analyticMapContinuous X Y f) := by
  ext z
  exact Point.mem_overOpen_map_iff f z U

/-- The algebraic product overlap underlying the deepest analytic Čech open. -/
def surfaceCechDeepestRegularOpen : surface.Opens :=
  (((pullback.fst curveToBase curveToBase ⁻¹ᵁ
          chart (differentialChartIndex 0)) ⊓
        (pullback.fst curveToBase curveToBase ⁻¹ᵁ
          chart (differentialChartIndex 1))) ⊓
      (pullback.snd curveToBase curveToBase ⁻¹ᵁ
        chart (differentialChartIndex 0))) ⊓
    (((pullback.fst curveToBase curveToBase ⁻¹ᵁ
          chart (differentialChartIndex 0)) ⊓
        (pullback.fst curveToBase curveToBase ⁻¹ᵁ
          chart (differentialChartIndex 1))) ⊓
      (pullback.snd curveToBase curveToBase ⁻¹ᵁ
        chart (differentialChartIndex 1)))

theorem regularAnalyticOpen_surfaceCechDeepestRegularOpen :
    regularAnalyticOpen surfaceVariety surfaceCechDeepestRegularOpen =
      surfaceCechDeepestOpen := by
  rfl

def openHolomorphicFunctionOfEq
    {X : Over (Spec (.of ℂ))} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : U = V)
    (f : OpenHolomorphicFunctions X d (.op U)) :
    OpenHolomorphicFunctions X d (.op V) := by
  subst V
  exact f

theorem openHolomorphicFunctionOfEq_apply
    {X : Over (Spec (.of ℂ))} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : U = V)
    (f : OpenHolomorphicFunctions X d (.op U)) (z : V) :
    (openHolomorphicFunctionOfEq h f).1 z =
      f.1 ⟨z.1, h ▸ z.2⟩ := by
  subst V
  rfl

/-- The adjusted regular representative as a section on the analytic curve overlap. -/
def curveCechAdjustedRepresentative :
    OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) :=
  openHolomorphicFunctionOfEq regularAnalyticOpen_curveCMOverlap
    (regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
      curveCechAdjustedRegularRepresentative)

theorem curveCechAdjustedRepresentative_apply
    (z : curveCechOverlap) :
    curveCechAdjustedRepresentative.1 z =
      Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative z.1 := by
  rw [curveCechAdjustedRepresentative,
    openHolomorphicFunctionOfEq_apply]
  rfl

/-- First-factor pullback of a regular curve-overlap section. -/
def surfaceFstRegularOverlapPullback (a : Γ(curve, curveCMOverlap)) :
    Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen) :=
  surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl
    curveCMOverlap surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans (inf_le_left.trans inf_le_right)) a

/-- Second-factor pullback of a regular curve-overlap section. -/
def surfaceSndRegularOverlapPullback (a : Γ(curve, curveCMOverlap)) :
    Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen) :=
  surfaceSectionPullback (pullback.snd curveToBase curveToBase)
    pullback.condition.symm curveCMOverlap
    surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right) a

def surfaceFstOverlapUnit :
    Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)ˣ :=
  Units.map (surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl
    curveCMOverlap surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans (inf_le_left.trans inf_le_right))).toMonoidHom
    curveCMOverlapYUUnit

def surfaceSndOverlapUnit :
    Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)ˣ :=
  Units.map (surfaceSectionPullback (pullback.snd curveToBase curveToBase)
    pullback.condition.symm curveCMOverlap surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right)).toMonoidHom
    curveCMOverlapYUUnit

def surfaceFstOverlapDifferential :
    KaehlerDifferential ℂ Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen) :=
  surfaceDifferentialPullback (pullback.fst curveToBase curveToBase) rfl
    curveCMOverlap surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans (inf_le_left.trans inf_le_right))
    (curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential)

def surfaceSndOverlapDifferential :
    KaehlerDifferential ℂ Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen) :=
  surfaceDifferentialPullback (pullback.snd curveToBase curveToBase)
    pullback.condition.symm curveCMOverlap surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right)
    (curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential)

theorem surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y :
    surfaceCechDeepestRegularOpen ≤ surfaceDifferentialOpen (1, 1) := by
  apply le_inf
  · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
  · exact inf_le_right.trans inf_le_right

theorem surfaceFstAdjusted_smul_differential :
    surfaceFstRegularOverlapPullback
        curveCechAdjustedRegularRepresentative •
      surfaceFstOverlapDifferential =
      -(↑(surfaceFstOverlapUnit⁻¹) :
          Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)) •
        KaehlerDifferential.D ℂ Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
          (surfaceFstOverlapUnit :
            Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)) := by
  have h := congrArg
    (surfaceDifferentialPullback
      (pullback.fst curveToBase curveToBase) rfl curveCMOverlap
      surfaceCechDeepestRegularOpen (by
        rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
        apply le_inf
        · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
        · exact inf_le_left.trans (inf_le_left.trans inf_le_right)))
    curveCechAdjustedRegularRepresentative_smul_differential
  rw [surfaceDifferentialPullback_smul',
    surfaceDifferentialPullback_smul_D] at h
  simpa [surfaceFstRegularOverlapPullback,
    surfaceFstOverlapUnit, surfaceFstOverlapDifferential]
    using h

theorem surfaceSndAdjusted_smul_differential :
    surfaceSndRegularOverlapPullback
        curveCechAdjustedRegularRepresentative •
      surfaceSndOverlapDifferential =
      -(↑(surfaceSndOverlapUnit⁻¹) :
          Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)) •
        KaehlerDifferential.D ℂ Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
          (surfaceSndOverlapUnit :
            Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)) := by
  have h := congrArg
    (surfaceDifferentialPullback
      (pullback.snd curveToBase curveToBase) pullback.condition.symm curveCMOverlap
      surfaceCechDeepestRegularOpen (by
        rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
        apply le_inf
        · exact inf_le_left.trans inf_le_right
        · exact inf_le_right.trans inf_le_right))
    curveCechAdjustedRegularRepresentative_smul_differential
  rw [surfaceDifferentialPullback_smul',
    surfaceDifferentialPullback_smul_D] at h
  simpa [surfaceSndRegularOverlapPullback,
    surfaceSndOverlapUnit, surfaceSndOverlapDifferential]
    using h

def surfaceOverlapUnits :
    Fin 2 → Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)ˣ :=
  ![surfaceFstOverlapUnit, surfaceSndOverlapUnit]

theorem surfaceAdjustedScaledWedge_eq_logarithmicForm :
    Algebra.DeRham.kaehlerWedge ℂ
        Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
        (surfaceFstRegularOverlapPullback
            curveCechAdjustedRegularRepresentative •
          surfaceFstOverlapDifferential)
        (surfaceSndRegularOverlapPullback
            curveCechAdjustedRegularRepresentative •
          surfaceSndOverlapDifferential) =
      Algebra.DeRham.logarithmicForm ℂ
        Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen) 2
        surfaceOverlapUnits := by
  rw [surfaceFstAdjusted_smul_differential,
    surfaceSndAdjusted_smul_differential,
    Algebra.DeRham.kaehlerWedge_smul_D_smul_D]
  simp only [Algebra.DeRham.logarithmicForm, surfaceOverlapUnits,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two]
  congr 1
  · ring
  · funext i
    fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem surfaceFstOverlapDifferential_eq_local :
    surfaceFstOverlapDifferential =
      surfacePulledCurveDifferential
        (pullback.fst curveToBase curveToBase) rfl 1
        surfaceCechDeepestRegularOpen
        (surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y.trans
          inf_le_left) := by
  unfold surfaceFstOverlapDifferential
  exact surfaceDifferentialPullback_restrict_curve
    (pullback.fst curveToBase curveToBase) rfl curveCMOverlap_le_y
    surfaceCechDeepestRegularOpen _ curveYDifferential

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem surfaceSndOverlapDifferential_eq_local :
    surfaceSndOverlapDifferential =
      surfacePulledCurveDifferential
        (pullback.snd curveToBase curveToBase) pullback.condition.symm 1
        surfaceCechDeepestRegularOpen
        (surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y.trans
          inf_le_right) := by
  unfold surfaceSndOverlapDifferential
  exact surfaceDifferentialPullback_restrict_curve
    (pullback.snd curveToBase curveToBase) pullback.condition.symm
    curveCMOverlap_le_y surfaceCechDeepestRegularOpen _ curveYDifferential

theorem surfaceOverlapWedge_eq_localTwoForm :
    Algebra.DeRham.kaehlerWedge ℂ
        Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
        surfaceFstOverlapDifferential
        surfaceSndOverlapDifferential =
      surfaceLocalTwoFormOn (1, 1) surfaceCechDeepestRegularOpen
        surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y := by
  rw [surfaceFstOverlapDifferential_eq_local,
    surfaceSndOverlapDifferential_eq_local]
  rfl

theorem surfaceGlobalHolomorphicTwoForm_restrict_deepest :
    surfaceHolomorphicTwoFormSheaf.obj.map
        (homOfLE (show surfaceCechDeepestOpen ≤ ⊤ from le_top)).op
        surfaceGlobalHolomorphicTwoForm =
      (toSheafify (Opens.grothendieckTopology _)
        (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app
          (.op surfaceCechDeepestOpen)
          (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.kaehlerWedge ℂ
              Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
              surfaceFstOverlapDifferential
              surfaceSndOverlapDifferential)) := by
  let V := surfaceDifferentialOpen (1, 1)
  let W := surfaceCechDeepestRegularOpen
  have hW : W ≤ V :=
    surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y
  have hg := surfaceGlobalHolomorphicTwoForm_restrict (1, 1)
  have hr := surfaceLocalSheafTwoFormOn_restrict (1, 1)
    (hV := le_rfl) hW
  calc
    _ = surfaceHolomorphicTwoFormSheaf.obj.map
          (regularAnalyticRestriction (Over.mk surfaceToBase) hW).op
          (surfaceHolomorphicTwoFormSheaf.obj.map
            (homOfLE (show surfaceAnalyticOpen V ≤ ⊤ from le_top)).op
            surfaceGlobalHolomorphicTwoForm) := by
      rw [← ConcreteCategory.comp_apply]
      rw [← surfaceHolomorphicTwoFormSheaf.obj.map_comp]
      rfl
    _ = surfaceHolomorphicTwoFormSheaf.obj.map
          (regularAnalyticRestriction (Over.mk surfaceToBase) hW).op
          (surfaceLocalSheafTwoFormOn (1, 1) V le_rfl) :=
      congrArg (fun s => surfaceHolomorphicTwoFormSheaf.obj.map
        (regularAnalyticRestriction (Over.mk surfaceToBase) hW).op s) hg
    _ = surfaceLocalSheafTwoFormOn (1, 1) W hW := hr
    _ = _ := by
      unfold surfaceLocalSheafTwoFormOn surfaceLocalHolomorphicTwoFormOn
      rw [surfaceOverlapWedge_eq_localTwoForm]
      dsimp only [W]
      rfl

/-- The two pulled overlap coordinates as actual holomorphic units on the
deepest product-chart intersection. -/
def surfaceHolomorphicOverlapUnits :
    Fin 2 → (OpenHolomorphicFunctions (Over.mk surfaceToBase) 2
      (.op surfaceCechDeepestOpen))ˣ :=
  fun i => Units.map
    (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
      surfaceCechDeepestRegularOpen).toMonoidHom
    (surfaceOverlapUnits i)

theorem surfaceFstAdjustedPullback_eq_regular :
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤ surfaceCechOuterOverlap by
          exact inf_le_left.trans inf_le_left)).op
        (surfaceFstCechOverlapPullback curveCechAdjustedRepresentative) =
      regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
        surfaceCechDeepestRegularOpen
        (surfaceFstRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) := by
  apply ContMDiffMap.ext
  intro z
  have hz : z.1.underlying ∈ surfaceCechDeepestRegularOpen := by
    exact z.2
  have hzfst : Point.map surfaceVarietyFst z.1 ∈ curveCechOverlap := by
    have hzo : z.1 ∈ surfaceCechOuterOverlap :=
      (show surfaceCechDeepestOpen ≤ surfaceCechOuterOverlap by
        exact inf_le_left.trans inf_le_left) z.2
    rw [← curveCechOverlap_comap_surfaceFst] at hzo
    exact hzo
  calc
    _ = curveCechAdjustedRepresentative.1
        ⟨Point.map surfaceVarietyFst z.1, hzfst⟩ := rfl
    _ = Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative
        (Point.map surfaceVarietyFst z.1) :=
      curveCechAdjustedRepresentative_apply _
    _ = Point.evaluate surfaceCechDeepestRegularOpen
        (surfaceFstRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) z.1 :=
      (evaluate_surfaceSectionPullback
        (pullback.fst curveToBase curveToBase) rfl curveCMOverlap
        surfaceCechDeepestRegularOpen _
        curveCechAdjustedRegularRepresentative z.1 hz).symm
    _ = _ := rfl

theorem surfaceSndAdjustedPullback_eq_regular :
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤
            surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 by
          apply le_inf
          · exact inf_le_left.trans inf_le_right
          · exact inf_le_right.trans inf_le_right)).op
        (surfaceSndCechOverlapPullback curveCechAdjustedRepresentative) =
      regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
        surfaceCechDeepestRegularOpen
        (surfaceSndRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) := by
  apply ContMDiffMap.ext
  intro z
  have hz : z.1.underlying ∈ surfaceCechDeepestRegularOpen := by
    exact z.2
  have hzsnd : Point.map surfaceVarietySnd z.1 ∈ curveCechOverlap := by
    have hzo : z.1 ∈ surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 :=
      (show surfaceCechDeepestOpen ≤
          surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 by
        apply le_inf
        · exact inf_le_left.trans inf_le_right
        · exact inf_le_right.trans inf_le_right) z.2
    rw [← curveCechOverlap_comap_surfaceSnd] at hzo
    exact hzo
  calc
    _ = curveCechAdjustedRepresentative.1
        ⟨Point.map surfaceVarietySnd z.1, hzsnd⟩ := rfl
    _ = Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative
        (Point.map surfaceVarietySnd z.1) :=
      curveCechAdjustedRepresentative_apply _
    _ = Point.evaluate surfaceCechDeepestRegularOpen
        (surfaceSndRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) z.1 :=
      (evaluate_surfaceSectionPullback
        (pullback.snd curveToBase curveToBase) pullback.condition.symm
        curveCMOverlap surfaceCechDeepestRegularOpen _
        curveCechAdjustedRegularRepresentative z.1 hz).symm
    _ = _ := rfl

theorem surfaceCechProductSection_adjusted_eq_regular :
    surfaceCechProductSection curveCechAdjustedRepresentative
        curveCechAdjustedRepresentative =
      regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
        surfaceCechDeepestRegularOpen
        (surfaceFstRegularOverlapPullback
            curveCechAdjustedRegularRepresentative *
          surfaceSndRegularOverlapPullback
            curveCechAdjustedRegularRepresentative) := by
  unfold surfaceCechProductSection
  rw [surfaceFstAdjustedPullback_eq_regular,
    surfaceSndAdjustedPullback_eq_regular, map_mul]

theorem surfaceTopFormProduct_eq_logarithmicFormSection :
    surfaceHolomorphicTopFormMultiplication.hom.app
        (.op surfaceCechDeepestOpen)
        (surfaceCechProductSection curveCechAdjustedRepresentative
          curveCechAdjustedRepresentative) =
      (toSheafify (Opens.grothendieckTopology _)
        (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app
          (.op surfaceCechDeepestOpen)
          (holomorphicLogarithmicForm (Over.mk surfaceToBase) 2
            (.op surfaceCechDeepestOpen) 2
            (fun i => Units.map
              (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
                surfaceCechDeepestRegularOpen).toMonoidHom
              (surfaceOverlapUnits i))) := by
  let w := regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
    surfaceCechDeepestRegularOpen 2
    (Algebra.DeRham.kaehlerWedge ℂ
      Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
      surfaceFstOverlapDifferential
      surfaceSndOverlapDifferential)
  calc
    _ = (toSheafify (Opens.grothendieckTopology _)
          (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app
          (.op surfaceCechDeepestOpen)
          (holomorphicFormFunctionMul (Over.mk surfaceToBase) 2
            (.op surfaceCechDeepestOpen) 2
            (surfaceCechProductSection curveCechAdjustedRepresentative
              curveCechAdjustedRepresentative) w) :=
      holomorphicTopFormMultiplicationSheaf_app_toSheafify
        (Over.mk surfaceToBase) 2 2 (.op surfaceCechDeepestOpen)
        surfaceGlobalHolomorphicTwoForm
        (surfaceCechProductSection curveCechAdjustedRepresentative
          curveCechAdjustedRepresentative) w
        surfaceGlobalHolomorphicTwoForm_restrict_deepest
    _ = _ := by
      apply congrArg
      dsimp only [w]
      rw [surfaceCechProductSection_adjusted_eq_regular]
      change holomorphicFormFunctionMul (Over.mk surfaceToBase) 2
          (.op (regularAnalyticOpen (Over.mk surfaceToBase)
            surfaceCechDeepestRegularOpen)) 2
          (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
            surfaceCechDeepestRegularOpen
            (surfaceFstRegularOverlapPullback
                curveCechAdjustedRegularRepresentative *
              surfaceSndRegularOverlapPullback
                curveCechAdjustedRegularRepresentative))
          (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.kaehlerWedge ℂ
              Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
              surfaceFstOverlapDifferential
              surfaceSndOverlapDifferential)) =
        holomorphicLogarithmicForm (Over.mk surfaceToBase) 2
          (.op (regularAnalyticOpen (Over.mk surfaceToBase)
            surfaceCechDeepestRegularOpen)) 2
          (fun i => Units.map
            (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
              surfaceCechDeepestRegularOpen).toMonoidHom
            (surfaceOverlapUnits i))
      calc
        _ = regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.kaehlerWedge ℂ
              Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen)
              (surfaceFstRegularOverlapPullback
                  curveCechAdjustedRegularRepresentative •
                surfaceFstOverlapDifferential)
              (surfaceSndRegularOverlapPullback
                  curveCechAdjustedRegularRepresentative •
                surfaceSndOverlapDifferential)) :=
          holomorphicFormFunctionMul_regular_kaehlerWedge
            (Over.mk surfaceToBase) 2 surfaceCechDeepestRegularOpen
            (surfaceFstRegularOverlapPullback
              curveCechAdjustedRegularRepresentative)
            (surfaceSndRegularOverlapPullback
              curveCechAdjustedRegularRepresentative)
            surfaceFstOverlapDifferential
            surfaceSndOverlapDifferential
        _ = regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.logarithmicForm ℂ
              Γ((Over.mk surfaceToBase).left, surfaceCechDeepestRegularOpen) 2
              surfaceOverlapUnits) :=
          congrArg (regularFormToHolomorphicForm
            (Over.mk surfaceToBase) 2 surfaceCechDeepestRegularOpen 2)
            surfaceAdjustedScaledWedge_eq_logarithmicForm
        _ = _ := by
          unfold regularFormToHolomorphicForm holomorphicLogarithmicForm
          simp only [LinearMap.comp_apply]
          apply congrArg
          exact Algebra.DeRham.map_logarithmicForm ℂ
            (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
              surfaceCechDeepestRegularOpen) 2
            surfaceOverlapUnits

/-- The four product charts, ordered as two successive two-open covers. -/
def surfaceCechIteratedCover :
    AnalyticIteratedCover surfaceVariety 2 where
  ambient := ![⊤, surfaceCechOuterOverlap, surfaceCechDeepestOpen]
  left := ![surfaceFstCechOpen 0, surfaceCechInnerOpen 0]
  right := ![surfaceFstCechOpen 1, surfaceCechInnerOpen 1]
  cover i := by
    fin_cases i
    · exact surfaceFstCechOpen_cover
    · exact surfaceCechInnerOpen_cover
  overlap i := by
    fin_cases i <;> rfl
  ambient_zero := rfl

@[simp]
theorem surfaceCechIteratedCover_deepest :
    surfaceCechIteratedCover.ambient 2 = surfaceCechDeepestOpen := by
  rfl

@[simp]
theorem surfaceCechIteratedCover_middle :
    surfaceCechIteratedCover.ambient 1 = surfaceCechOuterOverlap := by
  rfl

/-- The top-form multiple of the adjusted product representative is the
logarithmic section attached to the iterated product cover. -/
theorem surfaceTopFormProduct_eq_iteratedLogarithmicFormSection :
    surfaceHolomorphicTopFormMultiplication.hom.app
        (.op surfaceCechDeepestOpen)
        (surfaceCechProductSection curveCechAdjustedRepresentative
          curveCechAdjustedRepresentative) =
      analyticIteratedLogarithmicFormSection surfaceVariety
        surfaceCechIteratedCover surfaceHolomorphicOverlapUnits := by
  rw [surfaceTopFormProduct_eq_logarithmicFormSection]
  rfl

/-- After multiplying by the global top form, the adjusted holomorphic
external class is the nested transition class of the double logarithmic
section on the product cover. -/
theorem surfaceAdjustedCechExternalProductClass_comp_topForm :
    (surfaceHolomorphicCechExternalProductClass
        curveCechAdjustedRepresentative curveCechAdjustedRepresentative).comp
        (Abelian.Ext.mk₀ surfaceHolomorphicTopFormMultiplication)
        (show 2 + 0 = 2 from rfl) =
      analyticNestedTransitionExtClass surfaceVariety
        surfaceHolomorphicTwoFormSheaf
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceFstCechOpen_cover inf_le_left inf_le_left
        surfaceCechInnerOpen_cover
        (analyticIteratedLogarithmicFormSection surfaceVariety
          surfaceCechIteratedCover surfaceHolomorphicOverlapUnits) := by
  rw [surfaceHolomorphicCechExternalProductClass_comp_topForm]
  rw [surfaceTopFormProduct_eq_iteratedLogarithmicFormSection]

private theorem surfaceCechIteratedCover_topMap :
    surfaceCechIteratedCover.topMap =
      (analyticTopFreeAbelianSheafIso surfaceVariety).inv := by
  unfold AnalyticIteratedCover.topMap
  dsimp only [surfaceCechIteratedCover]
  have hi :
      homOfLE (show (⊤ : Opens (TopCat.of (ComplexPoint surfaceVariety))) ≤ ⊤ by
        rfl) = 𝟙 _ := Subsingleton.elim _ _
  rw [hi, analyticOpenFreeAbelianMap_id, Category.comp_id]

private theorem surfaceCechIteratedCover_stepExt_zero :
    surfaceCechIteratedCover.stepExt surfaceVariety 0 =
      (analyticCoverMayerVietorisSquare surfaceVariety
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        surfaceFstCechOpen_cover).shortComplex_shortExact.extClass
          (C := AnalyticAdditiveSheaf surfaceVariety) := by
  unfold AnalyticIteratedCover.stepExt
  dsimp only [surfaceCechIteratedCover]
  rfl

private theorem surfaceCechIteratedCover_stepExt_one :
    surfaceCechIteratedCover.stepExt surfaceVariety 1 =
      (analyticRelativeCoverMayerVietorisSquare surfaceVariety
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceCechOuterOverlap inf_le_left inf_le_left
        surfaceCechInnerOpen_cover).shortComplex_shortExact.extClass
          (C := AnalyticAdditiveSheaf surfaceVariety) := by
  unfold AnalyticIteratedCover.stepExt
  dsimp only [surfaceCechIteratedCover]
  rfl

/-- For this concrete two-step cover, the nested transition construction is
definitionally the generic iterated logarithmic transition class. -/
theorem surfaceNestedLogarithmicClass_eq_iterated :
    analyticNestedTransitionExtClass surfaceVariety
        surfaceHolomorphicTwoFormSheaf
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceFstCechOpen_cover inf_le_left inf_le_left
        surfaceCechInnerOpen_cover
        (analyticIteratedLogarithmicFormSection surfaceVariety
          surfaceCechIteratedCover surfaceHolomorphicOverlapUnits) =
      analyticIteratedLogarithmicTransitionExtClass surfaceVariety
        surfaceCechIteratedCover surfaceHolomorphicOverlapUnits := by
  unfold analyticIteratedLogarithmicTransitionExtClass
  rw [analyticIteratedTransitionExtClass_two]
  rw [surfaceCechIteratedCover_topMap,
    surfaceCechIteratedCover_stepExt_zero,
    surfaceCechIteratedCover_stepExt_one]
  unfold analyticNestedTransitionExtClass analyticRelativeTransitionExtClass
  dsimp only [surfaceCechIteratedCover]
  rfl

/-- The top-form image of the adjusted product class is precisely the
generic two-fold logarithmic transition class. -/
theorem surfaceAdjustedCechExternalProductClass_comp_topForm_eq_iterated :
    (surfaceHolomorphicCechExternalProductClass
        curveCechAdjustedRepresentative curveCechAdjustedRepresentative).comp
        (Abelian.Ext.mk₀ surfaceHolomorphicTopFormMultiplication)
        (show 2 + 0 = 2 from rfl) =
      analyticIteratedLogarithmicTransitionExtClass surfaceVariety
        surfaceCechIteratedCover surfaceHolomorphicOverlapUnits := by
  rw [surfaceAdjustedCechExternalProductClass_comp_topForm,
    surfaceNestedLogarithmicClass_eq_iterated]

/-- Nonvanishing of the explicit double-logarithmic class detects
nonvanishing of the adjusted holomorphic-function class. -/
theorem surfaceAdjustedCechExternalProductClass_ne_zero_of_iterated
    (h : analyticIteratedLogarithmicTransitionExtClass surfaceVariety
      surfaceCechIteratedCover surfaceHolomorphicOverlapUnits ≠ 0) :
    surfaceHolomorphicCechExternalProductClass
      curveCechAdjustedRepresentative curveCechAdjustedRepresentative ≠ 0 := by
  intro hz
  have heq := surfaceAdjustedCechExternalProductClass_comp_topForm_eq_iterated
  rw [hz, Abelian.Ext.zero_comp] at heq
  exact h heq.symm

end

end AlgebraicGeometry.ExplicitEllipticCandidate
