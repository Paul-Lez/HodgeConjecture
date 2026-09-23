/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernFrameLocalVanishing
/-!
# The local relative Chern class is the frame-change boundary

A reference frame defined on the whole chart has zero relative Chern class after
exact derived restriction. The actual frame-variation formula then identifies
the local Chern class with the singular boundary evaluated on the negative unit
relating the chosen frame to that reference. The original comparison is retained.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex
set_option autoImplicit false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  [IsIntegral X.left] [Smooth X.hom]
local instance localBoundaryAmbientDerived : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
local instance localBoundaryOpenDerived (U : Opens (TopCat.of (ComplexPoint X))) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) := HasDerivedCategory.standard _
variable (E : HolomorphicUnitExtension X d)
  {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
  (ℓ : E.middle.obj.obj (op U))
  (hℓ : E.projection.hom.app (op U) ℓ =
    (constantIntegerSheaf X).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (ℓ₂ : E.middle.obj.obj (op V))
  (hℓ₂ : E.projection.hom.app (op V) ℓ₂ =
    (constantIntegerSheaf X).obj.map (homOfLE (le_top : V ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

include hℓ in
/-- Relative to a frame extending across U, the local Chern class is the actual
singular boundary of the negative frame-change unit. -/
lemma HolomorphicUnitExtension.relativeChernClass_local_eq_neg_unit_boundary
    (cmp : RelativeChernComparison X d V)
    (w : (holomorphicUnitSheaf X d).obj.obj (op V))
    (hw : E.inclusion.hom.app (op V) w = ℓ₂ - E.middle.obj.map (homOfLE h).op ℓ) :
    (restrictToOpen X U).mapDerivedCategory.map
      (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (E.relativeChernClass V ℓ₂ hℓ₂ cmp)) =
    (restrictToOpen X U).mapDerivedCategory.map
      (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (hypercohomologyMap X
          (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X ((V : Set (ComplexPoint X))ᶜ))) 1
          (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
            ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
              Cocycle.equivHomShift.symm
                ((restrictedSingularOneCocycle X d V).precomp
                  ((analyticSingleFunctor X).map (TopCat.Sheaf.constHomOfSection
                    ((openRestrictionFunctor V).obj (holomorphicUnitSheaf X d))
                    ((openRestrictionTopEval V).inv.app (holomorphicUnitSheaf X d) (-w))))))))) := by
  let ℓ₁ := E.middle.obj.map (homOfLE h).op ℓ
  let hℓ₁ := E.projection_restrict_lift X h ℓ hℓ
  let F := (restrictToOpen X U).mapDerivedCategory
  have hb := E.relativeChernClass_sub_eq_neg_unit_boundary X V ℓ₁ ℓ₂ hℓ₁ hℓ₂ cmp w hw
  have hz := E.relativeChernClass_restrict_eq_zero X d h ℓ hℓ cmp
  have hc := congrArg (fun a => F.map
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q a)) hb
  let c₁ := E.relativeChernClass V ℓ₁ hℓ₁ cmp
  let c₂ := E.relativeChernClass V ℓ₂ hℓ₂ cmp
  have ha := congrArg F.map (hypercohomologyEquiv_sub X _ 1 c₂ c₁)
  have hm := F.map_sub
    (f := Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q c₂)
    (g := Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q c₁)
  have he := congrArg (fun b => F.map
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q c₂) - b) hz
  exact ((ha.trans hm).trans (he.trans (sub_zero _))).symm.trans hc
end AlgebraicGeometry.ComplexPoint
