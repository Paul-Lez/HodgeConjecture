import Other.AlgebraicGeometry.ExplicitEllipticSurfaceTopFormCech
import Other.AlgebraicGeometry.AnalyticIteratedTransitionClass
import Other.AlgebraicGeometry.ExplicitEllipticSurfaceInfinity
import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCotangentGeneration

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

@[expose] noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

attribute [local instance] regularSectionAlgebra

local instance checkSurfaceDoubleDlogAlgebra (V : surface.Opens) :
    Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

example : (Over.mk surfaceToBase).left = surface := by rfl

theorem check_curveYOpen_eq_chart : curveYOpen = chart 1 := by
  rfl

theorem check_regularAnalyticOpen_preimage
    {X Y : Over (Spec (.of ℂ))} (f : X ⟶ Y) (U : Y.left.Opens) :
    regularAnalyticOpen X (f.left ⁻¹ᵁ U) =
      (regularAnalyticOpen Y U).comap (analyticMapContinuous X Y f) := by
  ext z
  exact Point.mem_overOpen_map_iff f z U

/-- The algebraic product overlap underlying the deepest analytic Čech open. -/
def check_surfaceCechDeepestRegularOpen : surface.Opens :=
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

theorem check_regularAnalyticOpen_surfaceCechDeepestRegularOpen :
    regularAnalyticOpen surfaceVariety check_surfaceCechDeepestRegularOpen =
      surfaceCechDeepestOpen := by
  rfl

def check_openHolomorphicFunctionOfEq
    {X : Over (Spec (.of ℂ))} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : U = V)
    (f : OpenHolomorphicFunctions X d (.op U)) :
    OpenHolomorphicFunctions X d (.op V) := by
  subst V
  exact f

theorem check_openHolomorphicFunctionOfEq_apply
    {X : Over (Spec (.of ℂ))} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    {U V : Opens (TopCat.of (ComplexPoint X))} (h : U = V)
    (f : OpenHolomorphicFunctions X d (.op U)) (z : V) :
    (check_openHolomorphicFunctionOfEq h f).1 z =
      f.1 ⟨z.1, h ▸ z.2⟩ := by
  subst V
  rfl

/-- The adjusted regular representative as a section on the analytic curve overlap. -/
def check_curveCechAdjustedRepresentative :
    OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) :=
  check_openHolomorphicFunctionOfEq regularAnalyticOpen_curveCMOverlap
    (regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
      curveCechAdjustedRegularRepresentative)

theorem check_curveCechAdjustedRepresentative_apply
    (z : curveCechOverlap) :
    check_curveCechAdjustedRepresentative.1 z =
      Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative z.1 := by
  rw [check_curveCechAdjustedRepresentative,
    check_openHolomorphicFunctionOfEq_apply]
  rfl

/-- First-factor pullback of a regular curve-overlap section. -/
def check_surfaceFstRegularOverlapPullback (a : Γ(curve, curveCMOverlap)) :
    Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen) :=
  surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl
    curveCMOverlap check_surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans (inf_le_left.trans inf_le_right)) a

/-- Second-factor pullback of a regular curve-overlap section. -/
def check_surfaceSndRegularOverlapPullback (a : Γ(curve, curveCMOverlap)) :
    Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen) :=
  surfaceSectionPullback (pullback.snd curveToBase curveToBase)
    pullback.condition.symm curveCMOverlap
    check_surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right) a

def check_surfaceFstOverlapUnit :
    Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)ˣ :=
  Units.map (surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl
    curveCMOverlap check_surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans (inf_le_left.trans inf_le_right))).toMonoidHom
    curveCMOverlapYUUnit

def check_surfaceSndOverlapUnit :
    Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)ˣ :=
  Units.map (surfaceSectionPullback (pullback.snd curveToBase curveToBase)
    pullback.condition.symm curveCMOverlap check_surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right)).toMonoidHom
    curveCMOverlapYUUnit

def check_surfaceFstOverlapDifferential :
    KaehlerDifferential ℂ Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen) :=
  surfaceDifferentialPullback (pullback.fst curveToBase curveToBase) rfl
    curveCMOverlap check_surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans (inf_le_left.trans inf_le_right))
    (curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential)

def check_surfaceSndOverlapDifferential :
    KaehlerDifferential ℂ Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen) :=
  surfaceDifferentialPullback (pullback.snd curveToBase curveToBase)
    pullback.condition.symm curveCMOverlap check_surfaceCechDeepestRegularOpen (by
      rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
      apply le_inf
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right)
    (curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential)

theorem check_surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y :
    check_surfaceCechDeepestRegularOpen ≤ surfaceDifferentialOpen (1, 1) := by
  apply le_inf
  · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
  · exact inf_le_right.trans inf_le_right

theorem check_surfaceFstAdjusted_smul_differential :
    check_surfaceFstRegularOverlapPullback
        curveCechAdjustedRegularRepresentative •
      check_surfaceFstOverlapDifferential =
      -(↑(check_surfaceFstOverlapUnit⁻¹) :
          Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)) •
        KaehlerDifferential.D ℂ Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
          (check_surfaceFstOverlapUnit :
            Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)) := by
  have h := congrArg
    (surfaceDifferentialPullback
      (pullback.fst curveToBase curveToBase) rfl curveCMOverlap
      check_surfaceCechDeepestRegularOpen (by
        rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
        apply le_inf
        · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
        · exact inf_le_left.trans (inf_le_left.trans inf_le_right)))
    curveCechAdjustedRegularRepresentative_smul_differential
  rw [surfaceDifferentialPullback_smul',
    surfaceDifferentialPullback_smul_D] at h
  simpa [check_surfaceFstRegularOverlapPullback,
    check_surfaceFstOverlapUnit, check_surfaceFstOverlapDifferential]
    using h

theorem check_surfaceSndAdjusted_smul_differential :
    check_surfaceSndRegularOverlapPullback
        curveCechAdjustedRegularRepresentative •
      check_surfaceSndOverlapDifferential =
      -(↑(check_surfaceSndOverlapUnit⁻¹) :
          Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)) •
        KaehlerDifferential.D ℂ Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
          (check_surfaceSndOverlapUnit :
            Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)) := by
  have h := congrArg
    (surfaceDifferentialPullback
      (pullback.snd curveToBase curveToBase) pullback.condition.symm curveCMOverlap
      check_surfaceCechDeepestRegularOpen (by
        rw [curveCMOverlap_eq, Scheme.Hom.preimage_inf]
        apply le_inf
        · exact inf_le_left.trans inf_le_right
        · exact inf_le_right.trans inf_le_right))
    curveCechAdjustedRegularRepresentative_smul_differential
  rw [surfaceDifferentialPullback_smul',
    surfaceDifferentialPullback_smul_D] at h
  simpa [check_surfaceSndRegularOverlapPullback,
    check_surfaceSndOverlapUnit, check_surfaceSndOverlapDifferential]
    using h

def check_surfaceOverlapUnits :
    Fin 2 → Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)ˣ :=
  ![check_surfaceFstOverlapUnit, check_surfaceSndOverlapUnit]

theorem check_surfaceAdjustedScaledWedge_eq_logarithmicForm :
    Algebra.DeRham.kaehlerWedge ℂ
        Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
        (check_surfaceFstRegularOverlapPullback
            curveCechAdjustedRegularRepresentative •
          check_surfaceFstOverlapDifferential)
        (check_surfaceSndRegularOverlapPullback
            curveCechAdjustedRegularRepresentative •
          check_surfaceSndOverlapDifferential) =
      Algebra.DeRham.logarithmicForm ℂ
        Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen) 2
        check_surfaceOverlapUnits := by
  rw [check_surfaceFstAdjusted_smul_differential,
    check_surfaceSndAdjusted_smul_differential,
    Algebra.DeRham.kaehlerWedge_smul_D_smul_D]
  simp only [Algebra.DeRham.logarithmicForm, check_surfaceOverlapUnits,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two]
  congr 1
  · ring
  · funext i
    fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem check_surfaceFstOverlapDifferential_eq_local :
    check_surfaceFstOverlapDifferential =
      surfacePulledCurveDifferential
        (pullback.fst curveToBase curveToBase) rfl 1
        check_surfaceCechDeepestRegularOpen
        (check_surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y.trans
          inf_le_left) := by
  unfold check_surfaceFstOverlapDifferential
  exact surfaceDifferentialPullback_restrict_curve
    (pullback.fst curveToBase curveToBase) rfl curveCMOverlap_le_y
    check_surfaceCechDeepestRegularOpen _ curveYDifferential

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem check_surfaceSndOverlapDifferential_eq_local :
    check_surfaceSndOverlapDifferential =
      surfacePulledCurveDifferential
        (pullback.snd curveToBase curveToBase) pullback.condition.symm 1
        check_surfaceCechDeepestRegularOpen
        (check_surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y.trans
          inf_le_right) := by
  unfold check_surfaceSndOverlapDifferential
  exact surfaceDifferentialPullback_restrict_curve
    (pullback.snd curveToBase curveToBase) pullback.condition.symm
    curveCMOverlap_le_y check_surfaceCechDeepestRegularOpen _ curveYDifferential

theorem check_surfaceOverlapWedge_eq_localTwoForm :
    Algebra.DeRham.kaehlerWedge ℂ
        Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
        check_surfaceFstOverlapDifferential
        check_surfaceSndOverlapDifferential =
      surfaceLocalTwoFormOn (1, 1) check_surfaceCechDeepestRegularOpen
        check_surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y := by
  rw [check_surfaceFstOverlapDifferential_eq_local,
    check_surfaceSndOverlapDifferential_eq_local]
  rfl

theorem check_surfaceGlobalHolomorphicTwoForm_restrict_deepest :
    surfaceHolomorphicTwoFormSheaf.obj.map
        (homOfLE (show surfaceCechDeepestOpen ≤ ⊤ from le_top)).op
        surfaceGlobalHolomorphicTwoForm =
      (toSheafify (Opens.grothendieckTopology _)
        (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app
          (.op surfaceCechDeepestOpen)
          (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            check_surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.kaehlerWedge ℂ
              Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
              check_surfaceFstOverlapDifferential
              check_surfaceSndOverlapDifferential)) := by
  let V := surfaceDifferentialOpen (1, 1)
  let W := check_surfaceCechDeepestRegularOpen
  have hW : W ≤ V :=
    check_surfaceCechDeepestRegularOpen_le_surfaceDifferentialOpen_y_y
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
      rw [check_surfaceOverlapWedge_eq_localTwoForm]
      dsimp only [W]
      rfl

/-- The two pulled overlap coordinates as actual holomorphic units on the
deepest product-chart intersection. -/
def check_surfaceHolomorphicOverlapUnits :
    Fin 2 → (OpenHolomorphicFunctions (Over.mk surfaceToBase) 2
      (.op surfaceCechDeepestOpen))ˣ :=
  fun i => Units.map
    (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
      check_surfaceCechDeepestRegularOpen).toMonoidHom
    (check_surfaceOverlapUnits i)

theorem check_surfaceFstAdjustedPullback_eq_regular :
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤ surfaceCechOuterOverlap by
          exact inf_le_left.trans inf_le_left)).op
        (surfaceFstCechOverlapPullback check_curveCechAdjustedRepresentative) =
      regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
        check_surfaceCechDeepestRegularOpen
        (check_surfaceFstRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) := by
  apply ContMDiffMap.ext
  intro z
  have hz : z.1.underlying ∈ check_surfaceCechDeepestRegularOpen := by
    exact z.2
  have hzfst : Point.map surfaceVarietyFst z.1 ∈ curveCechOverlap := by
    have hzo : z.1 ∈ surfaceCechOuterOverlap :=
      (show surfaceCechDeepestOpen ≤ surfaceCechOuterOverlap by
        exact inf_le_left.trans inf_le_left) z.2
    rw [← curveCechOverlap_comap_surfaceFst] at hzo
    exact hzo
  calc
    _ = check_curveCechAdjustedRepresentative.1
        ⟨Point.map surfaceVarietyFst z.1, hzfst⟩ := rfl
    _ = Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative
        (Point.map surfaceVarietyFst z.1) :=
      check_curveCechAdjustedRepresentative_apply _
    _ = Point.evaluate check_surfaceCechDeepestRegularOpen
        (check_surfaceFstRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) z.1 :=
      (evaluate_surfaceSectionPullback
        (pullback.fst curveToBase curveToBase) rfl curveCMOverlap
        check_surfaceCechDeepestRegularOpen _
        curveCechAdjustedRegularRepresentative z.1 hz).symm
    _ = _ := rfl

theorem check_surfaceSndAdjustedPullback_eq_regular :
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤
            surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 by
          apply le_inf
          · exact inf_le_left.trans inf_le_right
          · exact inf_le_right.trans inf_le_right)).op
        (surfaceSndCechOverlapPullback check_curveCechAdjustedRepresentative) =
      regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
        check_surfaceCechDeepestRegularOpen
        (check_surfaceSndRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) := by
  apply ContMDiffMap.ext
  intro z
  have hz : z.1.underlying ∈ check_surfaceCechDeepestRegularOpen := by
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
    _ = check_curveCechAdjustedRepresentative.1
        ⟨Point.map surfaceVarietySnd z.1, hzsnd⟩ := rfl
    _ = Point.evaluate curveCMOverlap curveCechAdjustedRegularRepresentative
        (Point.map surfaceVarietySnd z.1) :=
      check_curveCechAdjustedRepresentative_apply _
    _ = Point.evaluate check_surfaceCechDeepestRegularOpen
        (check_surfaceSndRegularOverlapPullback
          curveCechAdjustedRegularRepresentative) z.1 :=
      (evaluate_surfaceSectionPullback
        (pullback.snd curveToBase curveToBase) pullback.condition.symm
        curveCMOverlap check_surfaceCechDeepestRegularOpen _
        curveCechAdjustedRegularRepresentative z.1 hz).symm
    _ = _ := rfl

theorem check_surfaceCechProductSection_adjusted_eq_regular :
    surfaceCechProductSection check_curveCechAdjustedRepresentative
        check_curveCechAdjustedRepresentative =
      regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
        check_surfaceCechDeepestRegularOpen
        (check_surfaceFstRegularOverlapPullback
            curveCechAdjustedRegularRepresentative *
          check_surfaceSndRegularOverlapPullback
            curveCechAdjustedRegularRepresentative) := by
  unfold surfaceCechProductSection
  rw [check_surfaceFstAdjustedPullback_eq_regular,
    check_surfaceSndAdjustedPullback_eq_regular, map_mul]

theorem check_surfaceTopFormProduct_eq_logarithmicFormSection :
    surfaceHolomorphicTopFormMultiplication.hom.app
        (.op surfaceCechDeepestOpen)
        (surfaceCechProductSection check_curveCechAdjustedRepresentative
          check_curveCechAdjustedRepresentative) =
      (toSheafify (Opens.grothendieckTopology _)
        (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app
          (.op surfaceCechDeepestOpen)
          (holomorphicLogarithmicForm (Over.mk surfaceToBase) 2
            (.op surfaceCechDeepestOpen) 2
            (fun i => Units.map
              (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
                check_surfaceCechDeepestRegularOpen).toMonoidHom
              (check_surfaceOverlapUnits i))) := by
  let w := regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
    check_surfaceCechDeepestRegularOpen 2
    (Algebra.DeRham.kaehlerWedge ℂ
      Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
      check_surfaceFstOverlapDifferential
      check_surfaceSndOverlapDifferential)
  calc
    _ = (toSheafify (Opens.grothendieckTopology _)
          (holomorphicDeRhamPresheaf (Over.mk surfaceToBase) 2 2)).app
          (.op surfaceCechDeepestOpen)
          (holomorphicFormFunctionMul (Over.mk surfaceToBase) 2
            (.op surfaceCechDeepestOpen) 2
            (surfaceCechProductSection check_curveCechAdjustedRepresentative
              check_curveCechAdjustedRepresentative) w) :=
      holomorphicTopFormMultiplicationSheaf_app_toSheafify
        (Over.mk surfaceToBase) 2 2 (.op surfaceCechDeepestOpen)
        surfaceGlobalHolomorphicTwoForm
        (surfaceCechProductSection check_curveCechAdjustedRepresentative
          check_curveCechAdjustedRepresentative) w
        check_surfaceGlobalHolomorphicTwoForm_restrict_deepest
    _ = _ := by
      apply congrArg
      dsimp only [w]
      rw [check_surfaceCechProductSection_adjusted_eq_regular]
      change holomorphicFormFunctionMul (Over.mk surfaceToBase) 2
          (.op (regularAnalyticOpen (Over.mk surfaceToBase)
            check_surfaceCechDeepestRegularOpen)) 2
          (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
            check_surfaceCechDeepestRegularOpen
            (check_surfaceFstRegularOverlapPullback
                curveCechAdjustedRegularRepresentative *
              check_surfaceSndRegularOverlapPullback
                curveCechAdjustedRegularRepresentative))
          (regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            check_surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.kaehlerWedge ℂ
              Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
              check_surfaceFstOverlapDifferential
              check_surfaceSndOverlapDifferential)) =
        holomorphicLogarithmicForm (Over.mk surfaceToBase) 2
          (.op (regularAnalyticOpen (Over.mk surfaceToBase)
            check_surfaceCechDeepestRegularOpen)) 2
          (fun i => Units.map
            (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
              check_surfaceCechDeepestRegularOpen).toMonoidHom
            (check_surfaceOverlapUnits i))
      calc
        _ = regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            check_surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.kaehlerWedge ℂ
              Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen)
              (check_surfaceFstRegularOverlapPullback
                  curveCechAdjustedRegularRepresentative •
                check_surfaceFstOverlapDifferential)
              (check_surfaceSndRegularOverlapPullback
                  curveCechAdjustedRegularRepresentative •
                check_surfaceSndOverlapDifferential)) :=
          holomorphicFormFunctionMul_regular_kaehlerWedge
            (Over.mk surfaceToBase) 2 check_surfaceCechDeepestRegularOpen
            (check_surfaceFstRegularOverlapPullback
              curveCechAdjustedRegularRepresentative)
            (check_surfaceSndRegularOverlapPullback
              curveCechAdjustedRegularRepresentative)
            check_surfaceFstOverlapDifferential
            check_surfaceSndOverlapDifferential
        _ = regularFormToHolomorphicForm (Over.mk surfaceToBase) 2
            check_surfaceCechDeepestRegularOpen 2
            (Algebra.DeRham.logarithmicForm ℂ
              Γ((Over.mk surfaceToBase).left, check_surfaceCechDeepestRegularOpen) 2
              check_surfaceOverlapUnits) :=
          congrArg (regularFormToHolomorphicForm
            (Over.mk surfaceToBase) 2 check_surfaceCechDeepestRegularOpen 2)
            check_surfaceAdjustedScaledWedge_eq_logarithmicForm
        _ = _ := by
          unfold regularFormToHolomorphicForm holomorphicLogarithmicForm
          simp only [LinearMap.comp_apply]
          apply congrArg
          exact Algebra.DeRham.map_logarithmicForm ℂ
            (regularToHolomorphicAlgHom (Over.mk surfaceToBase) 2
              check_surfaceCechDeepestRegularOpen) 2
            check_surfaceOverlapUnits

end

end AlgebraicGeometry.ExplicitEllipticCandidate
