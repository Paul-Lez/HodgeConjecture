/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMHolomorphicFunctions
public import Other.AlgebraicGeometry.ExplicitEllipticCurveCechResidueBridge

/-!
# Complex multiplication on the elliptic overlap

The order-four automorphism preserves the intersection of the two standard
affine charts.  Its pullback on holomorphic functions commutes with both chart
restrictions.  Consequently a hypothetical Cech coboundary for the adjusted
representative may be projected to the `-i` eigenspace on both charts.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

/-- Complex multiplication maps the algebraic overlap into itself. -/
theorem curveVarietyCMEnd_mem_curveCMOverlap
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveCMOverlap) :
    Point.map curveVarietyCMEnd z ∈ Point.overOpen curveCMOverlap := by
  rw [curveCMOverlap_eq] at hz ⊢
  exact ⟨curveVarietyCMEnd_mem_curveZOpen z hz.1,
    curveVarietyCMEnd_mem_curveYOpen z hz.2⟩

/-- Membership in the overlap is invariant under complex multiplication. -/
theorem curveVarietyCMEnd_mem_curveCMOverlap_iff
    (z : ComplexPoint curveVariety) :
    Point.map curveVarietyCMEnd z ∈ Point.overOpen curveCMOverlap ↔
      z ∈ Point.overOpen curveCMOverlap := by
  constructor
  · intro hz
    have h₁ := curveVarietyCMEnd_mem_curveCMOverlap _ hz
    have h₂ := curveVarietyCMEnd_mem_curveCMOverlap _ h₁
    have h₃ := curveVarietyCMEnd_mem_curveCMOverlap _ h₂
    rwa [curveVarietyCMEnd_four_apply] at h₃
  · exact curveVarietyCMEnd_mem_curveCMOverlap z

/-- The analytic CM self-map restricted to the chart overlap. -/
def curveCMOverlapAnalyticCMMap :
    regularAnalyticOpen curveVariety curveCMOverlap →
      regularAnalyticOpen curveVariety curveCMOverlap :=
  fun z ↦ ⟨Point.map curveVarietyCMEnd z.1,
    curveVarietyCMEnd_mem_curveCMOverlap z.1 z.2⟩

theorem contMDiff_curveCMOverlapAnalyticCMMap :
    ContMDiff (modelWithCornersSelf ℂ (Fin 1 → ℂ))
      (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω
      curveCMOverlapAnalyticCMMap := by
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
  have hfun : Subtype.val ∘ curveCMOverlapAnalyticCMMap =
      Point.map curveVarietyCMEnd ∘ Subtype.val := by rfl
  rw [hfun]
  exact h

/-- Pullback by CM on actual holomorphic functions of the overlap. -/
def curveCMOverlapHolomorphicCMEnd :
    OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveCMOverlap)) →ₐ[ℂ]
      OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveCMOverlap)) where
  toFun f := ⟨f.1 ∘ curveCMOverlapAnalyticCMMap,
    ContMDiff.comp f.2 contMDiff_curveCMOverlapAnalyticCMMap⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem curveCMOverlapHolomorphicCMEnd_apply
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)))
    (z : regularAnalyticOpen curveVariety curveCMOverlap) :
    (curveCMOverlapHolomorphicCMEnd f).1 z =
      f.1 ⟨Point.map curveVarietyCMEnd z.1,
        curveVarietyCMEnd_mem_curveCMOverlap z.1 z.2⟩ := by
  rfl

/-- Four iterations of the overlap CM map are the identity. -/
theorem curveCMOverlapAnalyticCMMap_four
    (z : regularAnalyticOpen curveVariety curveCMOverlap) :
    curveCMOverlapAnalyticCMMap
        (curveCMOverlapAnalyticCMMap
          (curveCMOverlapAnalyticCMMap
            (curveCMOverlapAnalyticCMMap z))) = z := by
  apply Subtype.ext
  exact curveVarietyCMEnd_four_apply z.1

/-- Pullback on overlap holomorphic functions has order dividing four. -/
theorem curveCMOverlapHolomorphicCMEnd_four
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap))) :
    curveCMOverlapHolomorphicCMEnd
        (curveCMOverlapHolomorphicCMEnd
          (curveCMOverlapHolomorphicCMEnd
            (curveCMOverlapHolomorphicCMEnd f))) = f := by
  apply ContMDiffMap.ext
  intro z
  exact congrArg f.1 (curveCMOverlapAnalyticCMMap_four z)

/-- The spectral projection of an overlap holomorphic function to the `-i`
eigenspace of complex multiplication. -/
def curveCMOverlapHolomorphicCMMinusPart
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap))) :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)) :=
  (1 / 4 : ℂ) • (f + Complex.I • curveCMOverlapHolomorphicCMEnd f -
    curveCMOverlapHolomorphicCMEnd (curveCMOverlapHolomorphicCMEnd f) -
    Complex.I • curveCMOverlapHolomorphicCMEnd
      (curveCMOverlapHolomorphicCMEnd (curveCMOverlapHolomorphicCMEnd f)))

/-- The overlap spectral projection lands in the `-i` eigenspace. -/
theorem curveCMOverlapHolomorphicCMEnd_minusPart
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap))) :
    curveCMOverlapHolomorphicCMEnd (curveCMOverlapHolomorphicCMMinusPart f) =
      -Complex.I • curveCMOverlapHolomorphicCMMinusPart f := by
  rw [curveCMOverlapHolomorphicCMMinusPart, map_smul, map_sub, map_sub,
    map_add, map_smul, map_smul, curveCMOverlapHolomorphicCMEnd_four]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- The overlap `-i` projector is additive. -/
theorem curveCMOverlapHolomorphicCMMinusPart_sub
    (f g : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap))) :
    curveCMOverlapHolomorphicCMMinusPart (f - g) =
      curveCMOverlapHolomorphicCMMinusPart f -
        curveCMOverlapHolomorphicCMMinusPart g := by
  simp only [curveCMOverlapHolomorphicCMMinusPart, map_sub, smul_sub]
  module

/-- A `-i` CM eigenfunction on the overlap is fixed by the spectral
projector. -/
theorem curveCMOverlapHolomorphicCMMinusPart_eq_self
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)))
    (hf : curveCMOverlapHolomorphicCMEnd f = -Complex.I • f) :
    curveCMOverlapHolomorphicCMMinusPart f = f := by
  have h2 : curveCMOverlapHolomorphicCMEnd
        (curveCMOverlapHolomorphicCMEnd f) =
      (-Complex.I * -Complex.I) • f := by
    calc
      curveCMOverlapHolomorphicCMEnd
          (curveCMOverlapHolomorphicCMEnd f) =
        curveCMOverlapHolomorphicCMEnd (-Complex.I • f) := congrArg _ hf
      _ = -Complex.I • curveCMOverlapHolomorphicCMEnd f := map_smul _ _ _
      _ = -Complex.I • (-Complex.I • f) := by rw [hf]
      _ = (-Complex.I * -Complex.I) • f := by rw [smul_smul]
  have h3 : curveCMOverlapHolomorphicCMEnd
        (curveCMOverlapHolomorphicCMEnd
          (curveCMOverlapHolomorphicCMEnd f)) =
      (-Complex.I * (-Complex.I * -Complex.I)) • f := by
    calc
      curveCMOverlapHolomorphicCMEnd
          (curveCMOverlapHolomorphicCMEnd
            (curveCMOverlapHolomorphicCMEnd f)) =
        curveCMOverlapHolomorphicCMEnd
          ((-Complex.I * -Complex.I) • f) := congrArg _ h2
      _ = (-Complex.I * -Complex.I) •
          curveCMOverlapHolomorphicCMEnd f := map_smul _ _ _
      _ = (-Complex.I * -Complex.I) • (-Complex.I • f) := by rw [hf]
      _ = (-Complex.I * (-Complex.I * -Complex.I)) • f := by
        rw [smul_smul]
        congr 1
        ring
  rw [curveCMOverlapHolomorphicCMMinusPart, h3, h2, hf]
  simp only [smul_sub, smul_add, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- Restriction from the Z chart commutes with CM pullback. -/
theorem curveZHolomorphicCMEnd_restrict_overlap
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen))) :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op
        (curveZHolomorphicCMEnd f) =
      curveCMOverlapHolomorphicCMEnd
        (holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op f) := by
  apply ContMDiffMap.ext
  intro z
  rfl

/-- Restriction from the Y chart commutes with CM pullback. -/
theorem curveYHolomorphicCMEnd_restrict_overlap
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op
        (curveYHolomorphicCMEnd f) =
      curveCMOverlapHolomorphicCMEnd
        (holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op f) := by
  apply ContMDiffMap.ext
  intro z
  rfl

/-- Restriction from the Z chart commutes with projection to the `-i`
eigenspace. -/
theorem curveZHolomorphicCMMinusPart_restrict_overlap
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen))) :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op
        (curveZHolomorphicCMMinusPart f) =
      curveCMOverlapHolomorphicCMMinusPart
        (holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op f) := by
  apply ContMDiffMap.ext
  intro z
  rfl

/-- Restriction from the Y chart commutes with projection to the `-i`
eigenspace. -/
theorem curveYHolomorphicCMMinusPart_restrict_overlap
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen))) :
    holomorphicRestrictionAlgHom curveVariety 1
        (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op
        (curveYHolomorphicCMMinusPart f) =
      curveCMOverlapHolomorphicCMMinusPart
        (holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op f) := by
  apply ContMDiffMap.ext
  intro z
  rfl

/-- The overlap restriction of the global CM endomorphism is the overlap
endomorphism constructed from the Y chart. -/
@[reassoc]
theorem curveCMOverlap_ι_curveCMEnd :
    curveCMOverlap.ι ≫ curveCMEnd =
      curveYCMOverlapEnd ≫ curveCMOverlap.ι := by
  calc
    curveCMOverlap.ι ≫ curveCMEnd =
        (curveCMOverlapToY ≫ curveYOpen.ι) ≫ curveCMEnd := by
          rw [curveCMOverlapToY_ι]
    _ = curveCMOverlapToY ≫ (curveYOpen.ι ≫ curveCMEnd) := by simp
    _ = curveCMOverlapToY ≫ (curveYCMChartIso.hom ≫ curveYOpen.ι) := by
          rw [curveYOpen_ι_curveCMEnd]
    _ = (curveCMOverlapToY ≫ curveYCMChartIso.hom) ≫ curveYOpen.ι := by simp
    _ = (curveYCMOverlapEnd ≫ curveCMOverlapToY) ≫ curveYOpen.ι := by
          rw [curveYCMOverlapEnd_toY]
    _ = curveYCMOverlapEnd ≫ curveCMOverlap.ι := by
          rw [Category.assoc, curveCMOverlapToY_ι]

/-- The overlap endomorphism, regarded as a morphism over the complex base. -/
def curveCMOverlapVarietyCMEnd :
    openScheme curveVariety curveCMOverlap ⟶
      openScheme curveVariety curveCMOverlap :=
  Over.homMk curveYCMOverlapEnd (by
    change curveYCMOverlapEnd ≫ curveCMOverlap.ι ≫ curveToBase =
      curveCMOverlap.ι ≫ curveToBase
    calc
      curveYCMOverlapEnd ≫ curveCMOverlap.ι ≫ curveToBase =
          (curveYCMOverlapEnd ≫ curveCMOverlap.ι) ≫ curveToBase := by simp
      _ = (curveCMOverlap.ι ≫ curveCMEnd) ≫ curveToBase := by
        rw [curveCMOverlap_ι_curveCMEnd]
      _ = curveCMOverlap.ι ≫ (curveCMEnd ≫ curveToBase) := by simp
      _ = curveCMOverlap.ι ≫ curveToBase := by rw [curveCMEnd_toBase])

/-- A point mapped by the overlap endomorphism and then included in the curve
is the global CM image of the included point. -/
theorem curveCMOverlapVarietyCMEnd_inclusion_apply
    (z : ComplexPoint (openScheme curveVariety curveCMOverlap)) :
    Point.map (openInclusion curveVariety curveCMOverlap)
        (Point.map curveCMOverlapVarietyCMEnd z) =
      Point.map curveVarietyCMEnd
        (Point.map (openInclusion curveVariety curveCMOverlap) z) := by
  rw [← Point.map_comp_apply, ← Point.map_comp_apply]
  rw [show curveCMOverlapVarietyCMEnd ≫
      openInclusion curveVariety curveCMOverlap =
        openInclusion curveVariety curveCMOverlap ≫ curveVarietyCMEnd by
    apply Over.OverMorphism.ext
    change curveYCMOverlapEnd ≫ curveCMOverlap.ι =
      curveCMOverlap.ι ≫ curveCMEnd
    exact curveCMOverlap_ι_curveCMEnd.symm]

/-- Evaluation intertwines the algebraic overlap pullback and the analytic CM
map on the ambient open subspace. -/
theorem evaluate_curveYCMOverlapRingEnd
    (s : Γ(curve, curveCMOverlap))
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveCMOverlap) :
    Point.evaluate curveCMOverlap (curveYCMOverlapRingEnd s) z =
      Point.evaluate curveCMOverlap s (Point.map curveVarietyCMEnd z) := by
  let w := asOpenPoint curveVariety curveCMOverlap z hz
  have hw : Point.map (openInclusion curveVariety curveCMOverlap) w = z := by
    exact Over.OverMorphism.ext
      (liftToOpen_fac curveVariety curveCMOverlap z hz)
  rw [← hw]
  rw [← curveCMOverlapVarietyCMEnd_inclusion_apply]
  let t : Γ(curveCMOverlap.toScheme, ⊤) := curveCMOverlap.topIso.inv s
  let t' : Γ(curveCMOverlap.toScheme, ⊤) :=
    curveYCMOverlapEnd.appTop t
  have hleft := evaluate_openEquiv curveVariety curveCMOverlap t' w
  have hright := evaluate_openEquiv curveVariety curveCMOverlap t
    (Point.map curveCMOverlapVarietyCMEnd w)
  have hmap := Point.evaluate_map curveCMOverlapVarietyCMEnd ⊤ t w
  have hchain := hleft.trans (hmap.symm.trans hright.symm)
  simp_rw [evaluate_eq (Y := curveVariety) curveCMOverlap.ι_image_top] at hchain
  have htransport :
      (curveCMOverlap.ι.appIso ⊤).inv ≫
          curveVariety.left.presheaf.map
            (eqToHom curveCMOverlap.ι_image_top.symm).op =
        curveCMOverlap.topIso.hom := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv,
      Scheme.Opens.topIso]
    change curveVariety.left.presheaf.map
        (eqToHom curveCMOverlap.ι_image_top.symm).op =
      curveVariety.left.presheaf.map
        (eqToHom curveCMOverlap.ι_image_top.symm).op
    rfl
  change Point.evaluate curveCMOverlap
      (((curveCMOverlap.ι.appIso ⊤).inv ≫
        curveVariety.left.presheaf.map
          (eqToHom curveCMOverlap.ι_image_top.symm).op) t')
        (Point.map (openInclusion curveVariety curveCMOverlap) w) =
    Point.evaluate curveCMOverlap
      (((curveCMOverlap.ι.appIso ⊤).inv ≫
        curveVariety.left.presheaf.map
          (eqToHom curveCMOverlap.ι_image_top.symm).op) t)
        (Point.map (openInclusion curveVariety curveCMOverlap)
          (Point.map curveCMOverlapVarietyCMEnd w)) at hchain
  rw [htransport] at hchain
  dsimp only [t] at hchain
  have hcancel : curveCMOverlap.topIso.hom
      (curveCMOverlap.topIso.inv s) = s :=
    curveCMOverlap.topIso.inv_hom_id_apply s
  have hcancelEval := congrArg
    (fun q : Γ(curve, curveCMOverlap) ↦
      Point.evaluate curveCMOverlap q
        (Point.map (openInclusion curveVariety curveCMOverlap)
          (Point.map curveCMOverlapVarietyCMEnd w))) hcancel
  have hout := hchain.trans hcancelEval
  change Point.evaluate curveCMOverlap
      (curveCMOverlap.topIso.hom
        (curveYCMOverlapEnd.appTop (curveCMOverlap.topIso.inv s)))
        (Point.map (openInclusion curveVariety curveCMOverlap) w) =
    Point.evaluate curveCMOverlap s
      (Point.map (openInclusion curveVariety curveCMOverlap)
        (Point.map curveCMOverlapVarietyCMEnd w))
  exact hout

/-- The adjusted analytic Cech representative has CM eigenvalue `-i`. -/
theorem curveCMOverlapHolomorphicCMEnd_adjusted :
    curveCMOverlapHolomorphicCMEnd
        (regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative) =
      -Complex.I •
        regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative := by
  apply ContMDiffMap.ext
  intro z
  change Point.evaluate curveCMOverlap
      curveCechAdjustedRegularRepresentative (Point.map curveVarietyCMEnd z.1) =
    -Complex.I * Point.evaluate curveCMOverlap
      curveCechAdjustedRegularRepresentative z.1
  rw [← evaluate_curveYCMOverlapRingEnd
    curveCechAdjustedRegularRepresentative z.1 z.2]
  rw [show curveYCMOverlapRingEnd curveCechAdjustedRegularRepresentative =
      -Complex.I • curveCechAdjustedRegularRepresentative by
    simp only [curveCechAdjustedRegularRepresentative, map_add,
      curveCechRegularRepresentative_cm, curveYCMOverlapRingEnd_YV]
    simp [Algebra.smul_def]
    ring]
  let ev := Point.evaluationHom (X := curveVariety) curveCMOverlap
    ⟨z.1, z.2⟩
  rw [← Point.evaluationHom_apply (X := curveVariety) curveCMOverlap
    ⟨z.1, z.2⟩ (-Complex.I • curveCechAdjustedRegularRepresentative),
    ← Point.evaluationHom_apply (X := curveVariety) curveCMOverlap
      ⟨z.1, z.2⟩ curveCechAdjustedRegularRepresentative]
  change ev (-Complex.I • curveCechAdjustedRegularRepresentative) =
    -Complex.I * ev curveCechAdjustedRegularRepresentative
  have hI := evaluate_regularSectionScalar curveVariety curveCMOverlap
    (-Complex.I) z.1 z.2
  have hIalg : ev (algebraMap ℂ Γ(curve, curveCMOverlap) (-Complex.I)) =
      -Complex.I := by
    rw [Point.evaluationHom_apply]
    exact hI
  rw [Algebra.smul_def, map_mul, hIalg]

/-- A hypothetical holomorphic two-chart coboundary for the adjusted
representative can be replaced by one whose two chart functions both have CM
eigenvalue `-i`.  This is the analytic reduction used in the pole argument. -/
theorem curveCechAdjustedCoboundary_project_to_cm_minus
    (fZ : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (fY : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveYOpen)))
    (h :
      holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op fZ -
        holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op fY =
        regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative) :
    holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_z).op
          (curveZHolomorphicCMMinusPart fZ) -
        holomorphicRestrictionAlgHom curveVariety 1
          (regularAnalyticRestriction curveVariety curveCMOverlap_le_y).op
          (curveYHolomorphicCMMinusPart fY) =
        regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
          curveCechAdjustedRegularRepresentative ∧
      curveZHolomorphicCMEnd (curveZHolomorphicCMMinusPart fZ) =
        -Complex.I • curveZHolomorphicCMMinusPart fZ ∧
      curveYHolomorphicCMEnd (curveYHolomorphicCMMinusPart fY) =
        -Complex.I • curveYHolomorphicCMMinusPart fY := by
  refine ⟨?_, curveZHolomorphicCMEnd_minusPart fZ,
    curveYHolomorphicCMEnd_minusPart fY⟩
  rw [curveZHolomorphicCMMinusPart_restrict_overlap,
    curveYHolomorphicCMMinusPart_restrict_overlap]
  rw [← curveCMOverlapHolomorphicCMMinusPart_sub, h]
  exact curveCMOverlapHolomorphicCMMinusPart_eq_self _
    curveCMOverlapHolomorphicCMEnd_adjusted

end AlgebraicGeometry.ExplicitEllipticCandidate
