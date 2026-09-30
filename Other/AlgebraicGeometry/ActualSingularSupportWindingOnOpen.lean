/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ActualSingularSupportBoundaryOnOpen
public import Other.AlgebraicGeometry.ChernWindingSupportedBoundary
public import Other.AlgebraicGeometry.RationalSupportBoundaryRelative
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf

/-! # Local supported-injective normalization of winding boundaries -/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace AlgebraicGeometry.ComplexPoint

local instance localSupportedWindingTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance localSupportedWindingParacompact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)
  (V : Opens (TopCat.of (ComplexPoint X)))

/-- The canonical local injective boundary maps to the positive winding class. -/
lemma complexSupportInjectiveSectionCohomologyEquiv_winding_boundary_on_open
    (g : C(ChernWinding.puncturedSpace (V : Set (ComplexPoint X)) Z, ℂ))
    (hg : ∀ y, g y ≠ 0)
    (h : ChernWinding.HasRationalWindingPeriod (V : Set (ComplexPoint X)) Z g hg) :
    let U : Opens (TopCat.of (ComplexPoint X)) := ⟨Zᶜ, hZ.isOpen_compl⟩
    let z := ChernWinding.openRawRationalWindingClass (TopCat.of (ComplexPoint X))
      (V ⊓ U) (g.comp (ChernWinding.topMap (openIntersectionPairIsoSupportComplement
        (TopCat.of (ComplexPoint X)) Z hZ V).hom.left))
      (fun y => hg ((openIntersectionPairIsoSupportComplement
        (TopCat.of (ComplexPoint X)) Z hZ V).hom.left y))
    let SS := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) U V (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))
    let SI := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) U V (ambientRationalInjectiveComplex X)
    let Γ := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V)
      |>.mapHomologicalComplex (.up ℤ)
    let f : SS ⟶ SI := by
      change (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X)) U
        (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).map Γ ⟶
        (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X)) U
          (ambientRationalInjectiveComplex X)).map Γ
      exact Γ.mapShortComplex.map
        (TopCat.Sheaf.supportRestrictionComplexShortComplexMap (TopCat.of (ComplexPoint X)) U
          (complexSingularToAmbientInjective X))
    let eI := CochainComplex.mappingCocone.shortExactHomologyIsoCone SI
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact
        (TopCat.of (ComplexPoint X)) U V _) 1 2 (by omega)
    complexSupportInjectiveSectionCohomologyEquiv (X := X) ⟨Z, hZ⟩ V 2
      (eI.inv (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr SI.g) 1
        (HomologicalComplex.homologyMap f.τ₃ 1
          (HomologicalComplex.homologyMap
            (openRawToSupportedSingularOutside (TopCat.of (ComplexPoint X)) U V) 1 z)))) =
    ChernWinding.windingRelativeClass (V : Set (ComplexPoint X)) Z h := by
  dsimp only
  let U : Opens (TopCat.of (ComplexPoint X)) := ⟨Zᶜ, hZ.isOpen_compl⟩
  let z := ChernWinding.openRawRationalWindingClass (TopCat.of (ComplexPoint X))
    (V ⊓ U) (g.comp (ChernWinding.topMap (openIntersectionPairIsoSupportComplement
      (TopCat.of (ComplexPoint X)) Z hZ V).hom.left))
    (fun y => hg ((openIntersectionPairIsoSupportComplement
      (TopCat.of (ComplexPoint X)) Z hZ V).hom.left y))
  let zS := HomologicalComplex.homologyMap
    (openRawToSupportedSingularOutside (TopCat.of (ComplexPoint X)) U V) 1 z
  have hn := actualSingularSupportBoundary_comp_injective_on_open X Z hZ V 2 zS
  dsimp only at hn
  have hwind := ChernWinding.supportedSingularSectionCohomologyEquivSupportComplement_winding_boundary
    (TopCat.of (ComplexPoint X)) Z hZ V g hg h
  dsimp only at hwind
  have hn' := congrArg (fun b =>
      (complexSupportInjectiveSectionCohomologyEquiv (X := X) ⟨Z, hZ⟩ V 2) b) hn
  exact hn'.trans ((complexSupportInjectiveSectionCohomologyEquiv_supported_singular
    X ⟨Z, hZ⟩ V 2 _).trans hwind)

end AlgebraicGeometry.ComplexPoint
