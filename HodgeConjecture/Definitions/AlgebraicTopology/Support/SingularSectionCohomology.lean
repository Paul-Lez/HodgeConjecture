/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionCone
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularFlasqueModel
public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenCone
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FlattenedSupport
/-!
# Supported singular-section cohomology on arbitrary opens

The kernel of restriction on singular cochain sheaves is compared to the relative singular
pair on an arbitrary open neighborhood. The construction composes the flasque kernel/cone
comparison, the canonical grading comparison, and the sheafification-unit cone comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})

/-- The literal intersection subspace and the complement of a support inside an open
are homeomorphic by regrouping subtype witnesses. -/
def openIntersectionSupportComplementHomeomorph (S : Set X) (hS : IsClosed S) (V : Opens X) :
    ↥(V ⊓ (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X)) ≃ₜ {v : V | v.1 ∉ S} where
  toEquiv := (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ V) (· ∉ S)).symm
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The actual open-inclusion pair is the actual support-complement pair, preserving
the ambient open pointwise. -/
def openIntersectionPairIsoSupportComplement (S : Set X) (hS : IsClosed S) (V : Opens X) :
    openInclusionPair X (Opens.infLELeft V (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X)) ≅
      neighborhoodSupportComplementPair (V : Set X) S where
  hom := TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨openIntersectionSupportComplementHomeomorph X S hS V,
      (openIntersectionSupportComplementHomeomorph X S hS V).continuous⟩) rfl
  inv := TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨(openIntersectionSupportComplementHomeomorph X S hS V).symm,
      (openIntersectionSupportComplementHomeomorph X S hS V).symm.continuous⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V] (U V : Opens X)

/-- `H^n_{X \ U}(V; ℚ) ≅ H^n(V, V ⊓ U; ℚ)`: the cohomology of sections over `V` of
`Γ_{X \ U}(C^•_sing)` is the rational singular cohomology of the pair `(V, V ⊓ U)`. -/
def supportedRationalSingularSectionCohomologyEquivRelative (n : ℕ) :
    -- `H^n_{X \ U}(V; ℚ) ≅ H^n(V, V ⊓ U; ℚ)`.
    ((((TopCat.Sheaf.supportEvaluation X
      -- Sections over the open `V`.
      V).mapHomologicalComplex ℤᵘᵖ).obj
      -- `Γ_{X \ U}` of the singular-cochain sheaf complex.
      (supportedRationalSingularCochainComplex X U))).homology (n : ℤ) ≃+
        -- `H^n` of the pair `(V, V ⊓ U)`.
        RelativeCohomology ℚ (openInclusionPair X (Opens.infLELeft V U)) n :=
  (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V
      (rationalSingularCochainComplex X) (fun _ => inferInstance) (n : ℤ)).addCommGroupIsoToAddEquiv
    |>.trans <|
  (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X
      (singularCochainSheafComplex ℚ X) (Opens.infLELeft V U))
        ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv
    |>.trans (openSingularSheafRestrictionConeCohomologyEquivRelative X (Opens.infLELeft V U) n)

/-- `H^n_S(V; ℚ) ≅ H^n(V, V \ S; ℚ)` for a closed `S ⊆ X`, through the explicit identification
of the pairs `(V, V ⊓ (X \ S))` and `(V, V \ S)`. -/
def supportedRationalSingularSectionCohomologyEquivSupportComplement
    (S : Set X) (hS : IsClosed S) (V : Opens X) (n : ℕ) :
    -- `H^n_S(V; ℚ) ≅ H^n(V, V \ S; ℚ)`.
    ((((TopCat.Sheaf.supportEvaluation X
      -- Sections over the open `V`.
      V).mapHomologicalComplex ℤᵘᵖ).obj
      -- `Γ_S` of the singular-cochain sheaf complex.
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ) ≃+
        -- `H^n` of the pair `(V, V \ S)`.
        RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n :=
  (supportedRationalSingularSectionCohomologyEquivRelative X ⟨Sᶜ, hS.isOpen_compl⟩ V n).trans
    (((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
      (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso
        (openIntersectionPairIsoSupportComplement X S hS V).symm))).toLinearEquiv.toAddEquiv)

end AlgebraicTopology.Singular
