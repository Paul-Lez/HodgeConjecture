/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCurveCechNonvanishing
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechProduct

/-!
# Fiber detection of the inner elliptic-surface Cech class

Restricting the product representative to a first-factor fiber turns its
inner surface Cech coboundary equation into the curve Cech coboundary
equation.  At a fiber where the first representative is nonzero, this proves
that the inner relative transition class is nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The constant self-map of the curve with value `p`. -/
def curveConstantMap (p : ComplexPoint curveVariety) :
    curveVariety ⟶ curveVariety :=
  Over.homMk (curveToBase ≫ p.left) (by
    have hp := Over.w p
    change p.left ≫ curveToBase = 𝟙 (Spec (CommRingCat.of ℂ)) at hp
    change (curveToBase ≫ p.left) ≫ curveToBase = curveToBase
    rw [Category.assoc, hp, Category.comp_id])

/-- The inclusion of the fiber over a fixed first elliptic-curve point. -/
def curveFirstFiberMap (p : ComplexPoint curveVariety) :
    curveVariety ⟶ surfaceVariety :=
  Over.homMk
    (pullback.lift (curveConstantMap p).left (𝟙 curve)
      (by exact (curveConstantMap p).w))
    (by
      change pullback.lift (curveConstantMap p).left (𝟙 curve) _ ≫
        (pullback.fst curveToBase curveToBase ≫ curveToBase) = curveToBase
      rw [← Category.assoc, pullback.lift_fst]
      exact (curveConstantMap p).w)

theorem curveFirstFiberMap_fst_hom (p : ComplexPoint curveVariety) :
    curveFirstFiberMap p ≫ surfaceVarietyFst = curveConstantMap p := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

theorem curveFirstFiberMap_snd_hom (p : ComplexPoint curveVariety) :
    curveFirstFiberMap p ≫ surfaceVarietySnd = 𝟙 curveVariety := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

@[simp] theorem curveConstantMap_apply (p : ComplexPoint curveVariety)
    (z : ComplexPoint curveVariety) :
    Point.map (curveConstantMap p) z = p := by
  apply Over.OverMorphism.ext
  change z.left ≫ (curveToBase ≫ p.left) = p.left
  rw [← Category.assoc]
  have hz := Over.w z
  change z.left ≫ curveToBase = 𝟙 (Spec (CommRingCat.of ℂ)) at hz
  rw [hz]
  exact Category.id_comp p.left

@[simp] theorem curveFirstFiberMap_fst (p : ComplexPoint curveVariety)
    (z : ComplexPoint curveVariety) :
    Point.map surfaceVarietyFst (Point.map (curveFirstFiberMap p) z) = p := by
  rw [← Point.map_comp_apply, curveFirstFiberMap_fst_hom,
    curveConstantMap_apply]

@[simp] theorem curveFirstFiberMap_snd (p : ComplexPoint curveVariety)
    (z : ComplexPoint curveVariety) :
    Point.map surfaceVarietySnd (Point.map (curveFirstFiberMap p) z) = z := by
  rw [← Point.map_comp_apply, curveFirstFiberMap_snd_hom, Point.map_id]

/-- A point where the adjusted overlap representative is nonzero. -/
theorem exists_curveCechAdjusted_nonzero_point :
    ∃ p : curveCechOverlap,
      curveCechAdjustedHolomorphicRepresentative.1 p ≠ 0 := by
  by_contra hex
  have h : ∀ p : curveCechOverlap,
      curveCechAdjustedHolomorphicRepresentative.1 p = 0 := by
    intro p
    by_contra hp
    exact hex ⟨p, hp⟩
  apply curveCechAdjustedHolomorphicRepresentative_not_coboundary
  refine ⟨0, 0, ?_⟩
  apply Subtype.ext
  funext p
  rw [curveCechCoboundary, map_zero, map_zero, sub_zero]
  change 0 = curveCechAdjustedHolomorphicRepresentative.1 p
  exact (h p).symm

/-- A chosen fiber on which the first adjusted representative is nonzero. -/
def curveCechAdjustedNonzeroPoint : curveCechOverlap :=
  exists_curveCechAdjusted_nonzero_point.choose

theorem curveCechAdjustedNonzeroPoint_value_ne_zero :
    curveCechAdjustedHolomorphicRepresentative.1
      curveCechAdjustedNonzeroPoint ≠ 0 :=
  exists_curveCechAdjusted_nonzero_point.choose_spec

/-- The inner product-chart open restricts on a first-factor overlap
fiber to the corresponding curve chart. -/
theorem surfaceCechInnerOpen_comap_curveFirstFiber
    (p : curveCechOverlap) (i : Fin 2) :
    (surfaceCechInnerOpen i).comap
        (analyticMapContinuous curveVariety surfaceVariety
          (curveFirstFiberMap p.1)) =
      curveCechOpen i := by
  ext z
  change
    ((Point.map surfaceVarietyFst
        (Point.map (curveFirstFiberMap p.1) z)).underlying ∈ chart 2 ∧
      (Point.map surfaceVarietyFst
        (Point.map (curveFirstFiberMap p.1) z)).underlying ∈ chart 1) ∧
      (Point.map surfaceVarietySnd
        (Point.map (curveFirstFiberMap p.1) z)).underlying ∈
          chart (differentialChartIndex i) ↔
    z.underlying ∈ chart (differentialChartIndex i)
  rw [curveFirstFiberMap_fst, curveFirstFiberMap_snd]
  exact and_iff_right p.2

/-- The deepest product overlap restricts on the chosen fiber to the
curve overlap. -/
theorem surfaceCechDeepestOpen_comap_curveFirstFiber
    (p : curveCechOverlap) :
    surfaceCechDeepestOpen.comap
        (analyticMapContinuous curveVariety surfaceVariety
          (curveFirstFiberMap p.1)) =
      curveCechOverlap := by
  change
    (surfaceCechInnerOpen 0).comap
        (analyticMapContinuous curveVariety surfaceVariety
          (curveFirstFiberMap p.1)) ⊓
      (surfaceCechInnerOpen 1).comap
        (analyticMapContinuous curveVariety surfaceVariety
          (curveFirstFiberMap p.1)) = curveCechOverlap
  rw [
    surfaceCechInnerOpen_comap_curveFirstFiber,
    surfaceCechInnerOpen_comap_curveFirstFiber]

/-- Restrict a holomorphic function on an inner surface chart to the
chosen first-factor fiber. -/
def surfaceInnerOpenFiberPullback (p : curveCechOverlap) (i : Fin 2)
    (f : OpenHolomorphicFunctions surfaceVariety 2
      (.op (surfaceCechInnerOpen i))) :
    OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen i)) :=
  openHolomorphicFunctionAddEquivOfEq
    (surfaceCechInnerOpen_comap_curveFirstFiber p i)
    ((holomorphicFunctionSheafToPushforward curveVariety surfaceVariety
      (curveFirstFiberMap p.1) 1 2).hom.app
        (.op (surfaceCechInnerOpen i)) f)

/-- Restrict a holomorphic function on the deepest product overlap to
the chosen first-factor fiber. -/
def surfaceDeepestOpenFiberPullback (p : curveCechOverlap)
    (f : OpenHolomorphicFunctions surfaceVariety 2
      (.op surfaceCechDeepestOpen)) :
    OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) :=
  openHolomorphicFunctionAddEquivOfEq
    (surfaceCechDeepestOpen_comap_curveFirstFiber p)
    ((holomorphicFunctionSheafToPushforward curveVariety surfaceVariety
      (curveFirstFiberMap p.1) 1 2).hom.app
        (.op surfaceCechDeepestOpen) f)

@[simp] theorem surfaceInnerOpenFiberPullback_apply
    (p : curveCechOverlap) (i : Fin 2)
    (f : OpenHolomorphicFunctions surfaceVariety 2
      (.op (surfaceCechInnerOpen i))) (z : curveCechOpen i) :
    (surfaceInnerOpenFiberPullback p i f).1 z =
      f.1 ⟨Point.map (curveFirstFiberMap p.1) z.1, by
        have hz : z.1 ∈ (surfaceCechInnerOpen i).comap
            (analyticMapContinuous curveVariety surfaceVariety
              (curveFirstFiberMap p.1)) := by
          rw [surfaceCechInnerOpen_comap_curveFirstFiber p i]
          exact z.2
        exact hz⟩ := by
  rw [surfaceInnerOpenFiberPullback,
    openHolomorphicFunctionAddEquivOfEq_apply]
  rfl

@[simp] theorem surfaceDeepestOpenFiberPullback_apply
    (p : curveCechOverlap)
    (f : OpenHolomorphicFunctions surfaceVariety 2
      (.op surfaceCechDeepestOpen)) (z : curveCechOverlap) :
    (surfaceDeepestOpenFiberPullback p f).1 z =
      f.1 ⟨Point.map (curveFirstFiberMap p.1) z.1, by
        have hz : z.1 ∈ surfaceCechDeepestOpen.comap
            (analyticMapContinuous curveVariety surfaceVariety
              (curveFirstFiberMap p.1)) := by
          rw [surfaceCechDeepestOpen_comap_curveFirstFiber p]
          exact z.2
        exact hz⟩ := by
  rw [surfaceDeepestOpenFiberPullback,
    openHolomorphicFunctionAddEquivOfEq_apply]
  rfl

/-- Fiber restriction commutes with the inner Cech restriction maps. -/
theorem surfaceFiberPullback_restrict_inner (p : curveCechOverlap)
    (i : Fin 2)
    (f : OpenHolomorphicFunctions surfaceVariety 2
      (.op (surfaceCechInnerOpen i))) :
    surfaceDeepestOpenFiberPullback p
        (holomorphicRestrictionAlgHom surfaceVariety 2
          (homOfLE (show surfaceCechDeepestOpen ≤ surfaceCechInnerOpen i by
            fin_cases i
            · exact inf_le_left
            · exact inf_le_right)).op f) =
      holomorphicRestrictionAlgHom curveVariety 1
        (homOfLE (show curveCechOverlap ≤ curveCechOpen i by
          fin_cases i <;> simp)).op
        (surfaceInnerOpenFiberPullback p i f) := by
  apply Subtype.ext
  funext z
  rw [surfaceDeepestOpenFiberPullback_apply,
    holomorphicRestrictionAlgHom_apply_of_le,
    surfaceInnerOpenFiberPullback_apply]
  rfl

/-- Fiber restriction of the product section is scalar multiplication
by the value of its first factor. -/
theorem surfaceDeepestOpenFiberPullback_product_apply
    (p : curveCechOverlap)
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap))
    (z : curveCechOverlap) :
    (surfaceDeepestOpenFiberPullback p (surfaceCechProductSection a b)).1 z =
      a.1 p * b.1 z := by
  rw [surfaceDeepestOpenFiberPullback_apply]
  change
    a.1 ⟨Point.map surfaceVarietyFst
        (Point.map (curveFirstFiberMap p.1) z.1), _⟩ *
      b.1 ⟨Point.map surfaceVarietySnd
        (Point.map (curveFirstFiberMap p.1) z.1), _⟩ = _
  congr 1
  · exact congrArg a.1 (Subtype.ext (curveFirstFiberMap_fst p.1 z.1))
  · exact congrArg b.1 (Subtype.ext (curveFirstFiberMap_snd p.1 z.1))

theorem surfaceDeepestOpenFiberPullback_sub (p : curveCechOverlap)
    (f g : OpenHolomorphicFunctions surfaceVariety 2
      (.op surfaceCechDeepestOpen)) :
    surfaceDeepestOpenFiberPullback p (f - g) =
      surfaceDeepestOpenFiberPullback p f -
        surfaceDeepestOpenFiberPullback p g := by
  unfold surfaceDeepestOpenFiberPullback
  rw [map_sub, map_sub]

theorem surfaceDeepestOpenFiberPullback_product
    (p : curveCechOverlap)
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    surfaceDeepestOpenFiberPullback p (surfaceCechProductSection a b) =
      a.1 p • b := by
  apply Subtype.ext
  funext z
  rw [surfaceDeepestOpenFiberPullback_product_apply]
  rfl

/-- The inner Mayer--Vietoris class of the adjusted external product is
already nonzero.  This is detected by one first-factor fiber and the
unconditional curve Cech nonvanishing theorem. -/
theorem surfaceAdjustedInnerTransitionClass_ne_zero :
    analyticRelativeTransitionExtClass surfaceVariety
      surfaceCechHolomorphicFunctionSheaf
      (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
      surfaceCechOuterOverlap inf_le_left inf_le_left
      surfaceCechInnerOpen_cover
      (surfaceCechProductSection
        curveCechAdjustedHolomorphicRepresentative
        curveCechAdjustedHolomorphicRepresentative) ≠ 0 := by
  intro hzero
  obtain ⟨f₀, f₁, h⟩ :=
    (analyticRelativeTransitionExtClass_eq_zero_iff surfaceVariety
      surfaceCechHolomorphicFunctionSheaf
      (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
      surfaceCechOuterOverlap inf_le_left inf_le_left
      surfaceCechInnerOpen_cover
      (surfaceCechProductSection
        curveCechAdjustedHolomorphicRepresentative
        curveCechAdjustedHolomorphicRepresentative)).mp hzero
  change
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE inf_le_left).op f₀ -
      holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE inf_le_right).op f₁ =
      surfaceCechProductSection
        curveCechAdjustedHolomorphicRepresentative
        curveCechAdjustedHolomorphicRepresentative at h
  let p := curveCechAdjustedNonzeroPoint
  let c : ℂ := curveCechAdjustedHolomorphicRepresentative.1 p
  have hc : c ≠ 0 := curveCechAdjustedNonzeroPoint_value_ne_zero
  have hp := congrArg (surfaceDeepestOpenFiberPullback p) h
  rw [surfaceDeepestOpenFiberPullback_sub,
    surfaceFiberPullback_restrict_inner,
    surfaceFiberPullback_restrict_inner,
    surfaceDeepestOpenFiberPullback_product] at hp
  apply curveCechAdjustedHolomorphicRepresentative_not_coboundary
  refine ⟨c⁻¹ • surfaceInnerOpenFiberPullback p 0 f₀,
    c⁻¹ • surfaceInnerOpenFiberPullback p 1 f₁, ?_⟩
  unfold curveCechCoboundary
  rw [map_smul, map_smul, ← smul_sub, hp]
  rw [smul_smul]
  change (c⁻¹ * c) • curveCechAdjustedHolomorphicRepresentative = _
  rw [inv_mul_cancel₀ hc, one_smul]

end AlgebraicGeometry.ExplicitEllipticCandidate
