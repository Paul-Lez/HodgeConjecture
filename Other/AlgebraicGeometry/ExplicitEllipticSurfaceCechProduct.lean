/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechCover
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceHolomorphicPullback

/-!
# The explicit Cech external product on the elliptic surface

For the two-chart cover of the explicit elliptic curve, two holomorphic functions on the
overlap determine a holomorphic function on the deepest member of the product cover: pull the
first function back along the first projection, pull the second one back along the second
projection, and multiply.  Applying the nested Mayer--Vietoris boundary gives an actual
degree-two sheaf extension on the surface.

This is the representative-level external product needed for the non-Hodge construction.  It
does not invoke a Kunneth theorem: the last theorem writes the class as the literal Yoneda
composition of the two Mayer--Vietoris extensions and the product section.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

/-- The two analytic opens used for the elliptic curve Cech cover. -/
abbrev curveCechOpen (i : Fin 2) :
    Opens (TopCat.of (ComplexPoint curveVariety)) :=
  curveAnalyticOpen (chart (differentialChartIndex i))

/-- The overlap of the two selected elliptic-curve charts. -/
abbrev curveCechOverlap : Opens (TopCat.of (ComplexPoint curveVariety)) :=
  curveCechOpen 0 ⊓ curveCechOpen 1

/-- The selected two opens cover the analytic elliptic curve. -/
theorem curveCechOpen_cover : curveCechOpen 0 ⊔ curveCechOpen 1 = ⊤ :=
  curveAnalyticOpen_cover

/-- The deepest open of the four-open surface cover. -/
abbrev surfaceCechDeepestOpen :
    Opens (TopCat.of (ComplexPoint surfaceVariety)) :=
  surfaceCechInnerOpen 0 ⊓ surfaceCechInnerOpen 1

/-- The inverse image of the curve overlap by the first projection is the outer overlap of the
surface cover. -/
theorem curveCechOverlap_comap_surfaceFst :
    curveCechOverlap.comap
        (ComplexPoint.analyticMapContinuous surfaceVariety curveVariety surfaceVarietyFst) =
      surfaceCechOuterOverlap := by
  ext z
  rfl

/-- The inverse image of the curve overlap by the second projection is the intersection of the
two second-factor members of the surface cover. -/
theorem curveCechOverlap_comap_surfaceSnd :
    curveCechOverlap.comap
        (ComplexPoint.analyticMapContinuous surfaceVariety curveVariety surfaceVarietySnd) =
      surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 := by
  ext z
  rfl

/-- Pull an overlap function back along the first projection. -/
def surfaceFstCechOverlapPullback
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    OpenHolomorphicFunctions surfaceVariety 2 (.op surfaceCechOuterOverlap) :=
  surfaceFstHolomorphicFunctionPullback.hom.app (.op curveCechOverlap) a

/-- Pull an overlap function back along the second projection. -/
def surfaceSndCechOverlapPullback
    (b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    OpenHolomorphicFunctions surfaceVariety 2
      (.op (surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1)) :=
  surfaceSndHolomorphicFunctionPullback.hom.app (.op curveCechOverlap) b

/-- Pull a function on one curve chart back to the corresponding second-factor surface
open. -/
def surfaceSndCechOpenPullback (i : Fin 2)
    (b : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen i))) :
    OpenHolomorphicFunctions surfaceVariety 2 (.op (surfaceSndCechOpen i)) :=
  surfaceSndHolomorphicFunctionPullback.hom.app (.op (curveCechOpen i)) b

/-- Pullback along the second projection commutes with restricting a chart function to the
curve overlap. -/
theorem surfaceSndCechOpenPullback_restrict_overlap (i : Fin 2)
    (b : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen i))) :
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 ≤
          surfaceSndCechOpen i by fin_cases i <;> simp)).op
        (surfaceSndCechOpenPullback i b) =
      surfaceSndCechOverlapPullback
        (holomorphicRestrictionAlgHom curveVariety 1
          (homOfLE (show curveCechOverlap ≤ curveCechOpen i by
            fin_cases i <;> simp)).op b) := by
  have h := congrArg (fun q => (ConcreteCategory.hom q) b)
    (surfaceSndHolomorphicFunctionPullback.hom.naturality
      (homOfLE (show curveCechOverlap ≤ curveCechOpen i by
        fin_cases i <;> simp)).op)
  exact h

/-- Two successive restrictions of holomorphic functions equal restriction along the composite
inclusion. -/
theorem holomorphicRestrictionAlgHom_trans_apply
    {U V W : Opens (TopCat.of (ComplexPoint surfaceVariety))}
    (hVU : V ≤ U) (hWV : W ≤ V)
    (f : OpenHolomorphicFunctions surfaceVariety 2 (.op U)) :
    holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE hWV).op
        (holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE hVU).op f) =
      holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (hWV.trans hVU)).op f := by
  change ((holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE hWV).op).comp
    (holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE hVU).op)) f = _
  rw [← holomorphicRestrictionAlgHom_comp]
  congr 2

/-- The product of the two pulled-back curve overlap functions on the deepest surface open. -/
def surfaceCechProductSection
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    OpenHolomorphicFunctions surfaceVariety 2 (.op surfaceCechDeepestOpen) :=
  holomorphicRestrictionAlgHom surfaceVariety 2
      (homOfLE (show surfaceCechDeepestOpen ≤ surfaceCechOuterOverlap by
        exact inf_le_left.trans inf_le_left)).op
      (surfaceFstCechOverlapPullback a) *
    holomorphicRestrictionAlgHom surfaceVariety 2
      (homOfLE (show surfaceCechDeepestOpen ≤
          surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 by
        apply le_inf
        · exact inf_le_left.trans inf_le_right
        · exact inf_le_right.trans inf_le_right)).op
      (surfaceSndCechOverlapPullback b)

/-- The additive Cech coboundary of functions on the two curve charts. -/
def curveCechCoboundary
    (b₀ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 0)))
    (b₁ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 1))) :
    OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) :=
  holomorphicRestrictionAlgHom curveVariety 1 (homOfLE inf_le_left).op b₀ -
    holomorphicRestrictionAlgHom curveVariety 1 (homOfLE inf_le_right).op b₁

/-- On one inner member of the surface cover, multiply the first overlap function by a
second-factor function defined on the corresponding curve chart. -/
def surfaceCechRightCoboundaryLocalSection
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap))
    (i : Fin 2)
    (b : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen i))) :
    OpenHolomorphicFunctions surfaceVariety 2 (.op (surfaceCechInnerOpen i)) :=
  holomorphicRestrictionAlgHom surfaceVariety 2
      (homOfLE (show surfaceCechInnerOpen i ≤ surfaceCechOuterOverlap from inf_le_left)).op
      (surfaceFstCechOverlapPullback a) *
    holomorphicRestrictionAlgHom surfaceVariety 2
      (homOfLE (show surfaceCechInnerOpen i ≤ surfaceSndCechOpen i from inf_le_right)).op
      (surfaceSndCechOpenPullback i b)

/-- Restricting the first factor of a local product section to the deepest open is independent
of which inner member was used. -/
theorem surfaceCechRightCoboundaryLocalSection_fst_restrict (i : Fin 2)
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤ surfaceCechInnerOpen i by
          fin_cases i
          · exact inf_le_left
          · exact inf_le_right)).op
        (holomorphicRestrictionAlgHom surfaceVariety 2
          (homOfLE (show surfaceCechInnerOpen i ≤ surfaceCechOuterOverlap from
            inf_le_left)).op (surfaceFstCechOverlapPullback a)) =
      holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤ surfaceCechOuterOverlap by
          exact inf_le_left.trans inf_le_left)).op
        (surfaceFstCechOverlapPullback a) := by
  exact holomorphicRestrictionAlgHom_trans_apply _ _ _

/-- Restricting the second factor of a local product section to the deepest open agrees with
first restricting the curve function to the curve overlap. -/
theorem surfaceCechRightCoboundaryLocalSection_snd_restrict (i : Fin 2)
    (b : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen i))) :
    holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤ surfaceCechInnerOpen i by
          fin_cases i
          · exact inf_le_left
          · exact inf_le_right)).op
        (holomorphicRestrictionAlgHom surfaceVariety 2
          (homOfLE (show surfaceCechInnerOpen i ≤ surfaceSndCechOpen i from
            inf_le_right)).op (surfaceSndCechOpenPullback i b)) =
      holomorphicRestrictionAlgHom surfaceVariety 2
        (homOfLE (show surfaceCechDeepestOpen ≤
          surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 by
            apply le_inf
            · exact inf_le_left.trans inf_le_right
            · exact inf_le_right.trans inf_le_right)).op
        (surfaceSndCechOverlapPullback
          (holomorphicRestrictionAlgHom curveVariety 1
            (homOfLE (show curveCechOverlap ≤ curveCechOpen i by
              fin_cases i <;> simp)).op b)) := by
  rw [holomorphicRestrictionAlgHom_trans_apply]
  rw [← surfaceSndCechOpenPullback_restrict_overlap i b]
  exact (holomorphicRestrictionAlgHom_trans_apply _ _ _).symm

/-- The product with a curve Cech coboundary is the inner Cech coboundary of the two local
product sections. -/
theorem surfaceCechProductSection_right_coboundary
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap))
    (b₀ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 0)))
    (b₁ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 1))) :
    holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE inf_le_left).op
        (surfaceCechRightCoboundaryLocalSection a 0 b₀) -
      holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE inf_le_right).op
        (surfaceCechRightCoboundaryLocalSection a 1 b₁) =
      surfaceCechProductSection a (curveCechCoboundary b₀ b₁) := by
  unfold surfaceCechRightCoboundaryLocalSection
  rw [map_mul, map_mul]
  rw [surfaceCechRightCoboundaryLocalSection_fst_restrict,
    surfaceCechRightCoboundaryLocalSection_fst_restrict,
    surfaceCechRightCoboundaryLocalSection_snd_restrict,
    surfaceCechRightCoboundaryLocalSection_snd_restrict]
  unfold surfaceCechProductSection curveCechCoboundary
    surfaceSndCechOverlapPullback
  rw [map_sub, map_sub]
  ring

@[simp]
theorem surfaceCechProductSection_zero_left
    (b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    surfaceCechProductSection 0 b = 0 := by
  unfold surfaceCechProductSection surfaceFstCechOverlapPullback
  rw [map_zero, map_zero, zero_mul]

@[simp]
theorem surfaceCechProductSection_zero_right
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    surfaceCechProductSection a 0 = 0 := by
  unfold surfaceCechProductSection surfaceSndCechOverlapPullback
  rw [map_zero, map_zero, mul_zero]

/-- The actual degree-one holomorphic Cech class represented by a curve overlap function. -/
def curveHolomorphicCechClass
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    Abelian.Ext.{1} (constantIntegerSheaf curveVariety)
      (holomorphicAdditiveFunctionSheaf curveVariety 1) 1 :=
  analyticTransitionExtClass curveVariety
    (holomorphicAdditiveFunctionSheaf curveVariety 1)
    (curveCechOpen 0) (curveCechOpen 1) curveCechOpen_cover a

/-- The representative-level external product of two curve holomorphic Cech classes. -/
def surfaceHolomorphicCechExternalProductClass
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      surfaceCechHolomorphicFunctionSheaf 2 :=
  surfaceHolomorphicNestedTransitionClass (surfaceCechProductSection a b)

@[simp]
theorem surfaceHolomorphicCechExternalProductClass_zero_left
    (b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    surfaceHolomorphicCechExternalProductClass 0 b = 0 := by
  rw [surfaceHolomorphicCechExternalProductClass,
    surfaceCechProductSection_zero_left]
  exact analyticNestedTransitionExtClass_zero surfaceVariety
    surfaceCechHolomorphicFunctionSheaf
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
    surfaceFstCechOpen_cover inf_le_left inf_le_left surfaceCechInnerOpen_cover

@[simp]
theorem surfaceHolomorphicCechExternalProductClass_zero_right
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    surfaceHolomorphicCechExternalProductClass a 0 = 0 := by
  rw [surfaceHolomorphicCechExternalProductClass,
    surfaceCechProductSection_zero_right]
  exact analyticNestedTransitionExtClass_zero surfaceVariety
    surfaceCechHolomorphicFunctionSheaf
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
    surfaceFstCechOpen_cover inf_le_left inf_le_left surfaceCechInnerOpen_cover

/-- The external product is zero when its second curve representative is an actual Cech
coboundary.  This is the first descent step from representatives to curve `H¹(ᵊ)`: it is
proved inside the inner Mayer--Vietoris extension, without any acyclicity assumption. -/
theorem surfaceHolomorphicCechExternalProductClass_right_coboundary
    (a : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap))
    (b₀ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 0)))
    (b₁ : OpenHolomorphicFunctions curveVariety 1 (.op (curveCechOpen 1))) :
    surfaceHolomorphicCechExternalProductClass a (curveCechCoboundary b₀ b₁) = 0 := by
  have hinner := analyticRelativeTransitionExtClass_coboundary (Over.mk surfaceToBase)
    surfaceCechHolomorphicFunctionSheaf
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1) surfaceCechOuterOverlap
    inf_le_left inf_le_left surfaceCechInnerOpen_cover
    (surfaceCechRightCoboundaryLocalSection a 0 b₀)
    (surfaceCechRightCoboundaryLocalSection a 1 b₁)
  change analyticRelativeTransitionExtClass (Over.mk surfaceToBase)
      surfaceCechHolomorphicFunctionSheaf
      (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1) surfaceCechOuterOverlap
      inf_le_left inf_le_left surfaceCechInnerOpen_cover
      (holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE inf_le_left).op
          (surfaceCechRightCoboundaryLocalSection a 0 b₀) -
        holomorphicRestrictionAlgHom surfaceVariety 2 (homOfLE inf_le_right).op
          (surfaceCechRightCoboundaryLocalSection a 1 b₁)) = 0 at hinner
  rw [surfaceCechProductSection_right_coboundary] at hinner
  unfold surfaceHolomorphicCechExternalProductClass
    surfaceHolomorphicNestedTransitionClass analyticNestedTransitionExtClass
  dsimp only
  rw [hinner, Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]

/-- The first Mayer--Vietoris extension in the surface product cover. -/
def surfaceCechOuterBoundaryExtClass :
    Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf surfaceVariety ⊤)
      (analyticOpenFreeAbelianSheaf surfaceVariety surfaceCechOuterOverlap) 1 :=
  (analyticCoverMayerVietorisSquare surfaceVariety
    (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
    surfaceFstCechOpen_cover).shortComplex_shortExact.extClass
      (C := AnalyticAdditiveSheaf surfaceVariety)

/-- The second Mayer--Vietoris extension in the surface product cover. -/
def surfaceCechInnerBoundaryExtClass :
    Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf surfaceVariety surfaceCechOuterOverlap)
      (analyticOpenFreeAbelianSheaf surfaceVariety surfaceCechDeepestOpen) 1 :=
  (analyticRelativeCoverMayerVietorisSquare surfaceVariety
    (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1) surfaceCechOuterOverlap
    inf_le_left inf_le_left surfaceCechInnerOpen_cover).shortComplex_shortExact.extClass
      (C := AnalyticAdditiveSheaf surfaceVariety)

/-- The universal degree-two Yoneda boundary of the explicit product cover. -/
def surfaceCechYonedaBoundaryExtClass :
    Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      (analyticOpenFreeAbelianSheaf surfaceVariety surfaceCechDeepestOpen) 2 :=
  (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf surfaceVariety)
      (analyticTopFreeAbelianSheafIso surfaceVariety).inv).comp
    (surfaceCechOuterBoundaryExtClass.comp surfaceCechInnerBoundaryExtClass
      (show 1 + 1 = 2 from rfl)) (show 0 + 2 = 2 from rfl)

/-- The explicit Cech external product is literally evaluation of the two-fold Yoneda
boundary on the product section. -/
theorem surfaceHolomorphicCechExternalProductClass_eq_yoneda
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap)) :
    surfaceHolomorphicCechExternalProductClass a b =
      surfaceCechYonedaBoundaryExtClass.comp
        (Abelian.Ext.mk₀ (ComplexPoint.analyticSectionSheafHom surfaceVariety
          surfaceCechHolomorphicFunctionSheaf surfaceCechDeepestOpen
          (surfaceCechProductSection a b)))
        (show 2 + 0 = 2 from rfl) := by
  let a₀ : Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      (analyticOpenFreeAbelianSheaf surfaceVariety ⊤) 0 :=
    Abelian.Ext.mk₀ (ComplexPoint.analyticTopFreeAbelianSheafIso surfaceVariety).inv
  let δ₀ := surfaceCechOuterBoundaryExtClass
  let δ₁ := surfaceCechInnerBoundaryExtClass
  let s : Abelian.Ext.{1}
      (analyticOpenFreeAbelianSheaf surfaceVariety surfaceCechDeepestOpen)
      surfaceCechHolomorphicFunctionSheaf 0 :=
    Abelian.Ext.mk₀ (ComplexPoint.analyticSectionSheafHom surfaceVariety
      surfaceCechHolomorphicFunctionSheaf surfaceCechDeepestOpen
      (surfaceCechProductSection a b))
  change a₀.comp (δ₀.comp (δ₁.comp s (show 1 + 0 = 1 from rfl))
      (show 1 + 1 = 2 from rfl)) (show 0 + 2 = 2 from rfl) =
    (a₀.comp (δ₀.comp δ₁ (show 1 + 1 = 2 from rfl))
      (show 0 + 2 = 2 from rfl)).comp s (show 2 + 0 = 2 from rfl)
  rw [← Abelian.Ext.comp_assoc δ₀ δ₁ s
    (show 1 + 1 = 2 from rfl) (show 1 + 0 = 1 from rfl)
    (show 1 + 1 = 2 from rfl)]
  exact (Abelian.Ext.comp_assoc a₀ (δ₀.comp δ₁ rfl) s
    (show 0 + 2 = 2 from rfl) (show 2 + 0 = 2 from rfl)
    (show 0 + 2 = 2 from rfl)).symm

end AlgebraicGeometry.ExplicitEllipticCandidate
