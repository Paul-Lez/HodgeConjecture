/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingCohomologyNaturality
public import Other.AlgebraicTopology.SupportedSingularBoundaryRelative
public import Other.AlgebraicTopology.OpenRawBoundaryComparison
public import Other.AlgebraicTopology.TopOpenRelativeCochainNormalization

/-!
# Winding normalization of the actual local supported-singular boundary

The positive kernel boundary, transported by the existing local relative
comparison and its literal support-complement pair isomorphism, is the existing
winding relative class. This does not include the separate negative sign in the
rational-support-to-injective comparison or the Cartier frame difference.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace ChernWinding
variable (X : TopCat.{0})

/-- The actual rational winding class transported to raw cochains on an open set. -/
def openRawRationalWindingClass (V : Opens X) (g : C(TopCat.of V, ℂ)) (hg : ∀ y, g y ≠ 0) :
    ((openRawSingularCochainComplex ℚ X V).extend ComplexShape.embeddingUpNat).homology (1 : ℤ) :=
  (openRawCochainHomologyEquivDual ℚ X V 1).symm (rationalWindingIntCohomologyClass g hg)

/-- The raw winding class commutes with literal restriction to a smaller open. -/
lemma openRawRationalWindingClass_restriction {V W : Opens X} (i : W ⟶ V)
    (g : C(TopCat.of V, ℂ)) (hg : ∀ y, g y ≠ 0) :
    HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (openRawSingularRestriction ℚ X i)
        ComplexShape.embeddingUpNat) 1 (openRawRationalWindingClass X V g hg) =
    openRawRationalWindingClass X W
      (g.comp (topMap ((Opens.toTopCat X).map i)))
      (fun y => hg ((Opens.toTopCat X).map i y)) := by
  apply (openRawCochainHomologyEquivDual ℚ X W 1).injective
  rw [openRawCochainHomologyEquivDual_restriction]
  simp only [openRawRationalWindingClass, AddEquiv.apply_symm_apply]
  exact rationalWindingIntCohomologyClass_naturality g hg
    ((Opens.toTopCat X).map i) (fun y => hg ((Opens.toTopCat X).map i y))

variable [T2Space X] [∀ W : Opens X, ParacompactSpace W]
  (S : Set X) (hS : IsClosed S) (V : Opens X)

/-- Positive actual supported-singular boundaries give the existing positive local
winding class, through the literal intersection/support-complement pair isomorphism. -/
theorem supportedSingularSectionCohomologyEquivSupportComplement_winding_boundary
    (g : C(puncturedSpace (V : Set X) S, ℂ)) (hg : ∀ y, g y ≠ 0)
    (h : HasRationalWindingPeriod (V : Set X) S g hg) :
    let U : Opens X := ⟨Sᶜ, hS.isOpen_compl⟩
    let q := openIntersectionPairIsoSupportComplement X S hS V
    let z := openRawRationalWindingClass X (V ⊓ U) (g.comp (topMap q.hom.left))
      (fun y => hg (q.hom.left y))
    supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V 2
      ((supportedSingularKernelHomologyIsoCone X U V 2).inv
        (HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr
            (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex X U V
              (rationalSingularCochainComplex X)).g) 1
          (HomologicalComplex.homologyMap (openRawToSupportedSingularOutside X U V) 1 z))) =
    windingRelativeClass (V : Set X) S h := by
  dsimp only
  let U : Opens X := ⟨Sᶜ, hS.isOpen_compl⟩
  let q := openIntersectionPairIsoSupportComplement X S hS V
  let β := rationalWindingIntCohomologyClass g hg
  let β' := rationalWindingIntCohomologyClass (g.comp (topMap q.hom.left))
    (fun y => hg (q.hom.left y))
  let z := openRawRationalWindingClass X (V ⊓ U) (g.comp (topMap q.hom.left))
    (fun y => hg (q.hom.left y))
  have hz : openRawCochainHomologyEquivDual ℚ X (V ⊓ U) 1 z = β' :=
    AddEquiv.apply_symm_apply _ _
  have hβ : HomologicalComplex.homologyMap
      (relativeDualCochainShortComplexIntMap ℚ q.hom).τ₃ 1 β = β' :=
    rationalWindingIntCohomologyClass_naturality g hg q.hom.left (fun y => hg (q.hom.left y))
  have hcanon : relativeCochainConeCohomologyEquivCanonical ℚ (supportPair (V : Set X) S) 2
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (relativeCochainRestrictionInt ℚ (supportPair (V : Set X) S))) 1 β) =
      windingRelativeClass (V : Set X) S h := by
    exact (relativeCochainConeCohomologyEquiv_eq_canonical_of_boundary ℚ
      (supportPair (V : Set X) S) 2 β).symm.trans
      (relativeCochainConeCohomologyEquiv_boundary_rationalWinding (V : Set X) S g hg h)
  have hrel : relativeCochainConeCohomologyEquivCanonical ℚ
      (openInclusionPair X (Opens.infLELeft V U)) 2
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (relativeCochainRestrictionInt ℚ (openInclusionPair X (Opens.infLELeft V U)))) 1 β') =
      relativeCohomologyMap ℚ 2 q.hom (windingRelativeClass (V : Set X) S h) := by
    have hn := relativeCochainConeCohomologyEquivCanonical_boundary_naturality ℚ q.hom 2 β
    have hc := congrArg (fun b => relativeCochainConeCohomologyEquivCanonical ℚ
      (openInclusionPair X (Opens.infLELeft V U)) 2
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (relativeCochainRestrictionInt ℚ (openInclusionPair X (Opens.infLELeft V U)))) 1 b)) hβ
    exact hc.symm.trans (hn.trans (congrArg (relativeCohomologyMap ℚ 2 q.hom) hcanon))
  have hraw := openRawSingularRestrictionConeCohomologyEquivRelative_boundary ℚ X
    (Opens.infLELeft V U) 2 z
  have hz' := congrArg (fun b => relativeCochainConeCohomologyEquivCanonical ℚ
    (openInclusionPair X (Opens.infLELeft V U)) 2
    (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr
        (relativeCochainRestrictionInt ℚ (openInclusionPair X (Opens.infLELeft V U)))) 1 b)) hz
  have hlocal := (supportedSingularSectionCohomologyEquivRelative_boundary X U V 2 z).trans
    (hraw.trans (hz'.trans hrel))
  have hmain := congrArg (relativeCohomologyMap ℚ 2 q.inv) hlocal
  refine hmain.trans ?_
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, Iso.inv_hom_id,
    relativeCohomologyMap_id, LinearMap.id_apply]

end ChernWinding
