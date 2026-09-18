/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.LocalSupportVanishing
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FiniteFiltrationVanishing

/-!
# Unique extension across the singular boundary of a closed subvariety

The canonical finite smooth filtration and its layerwise vanishing give the singular
boundary zero supported cohomology below `2(p+1)`, in particular in degrees `2p` and
`2p+1`. The nested-support localization sequence then makes restriction from the full
component support to its smooth-locus ambient open an isomorphism in degree `2p`, whose
inverse is the unique extension operation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

include hi in
/-- `H^n_{Z_sing,k(ℂ)}(X(ℂ); ℚ) = 0` for `n < 2(p + 1)`, where `Z_sing,k` is the `k`-th stage of
the finite smooth filtration of `Z_sing` (so `Z_sing,0 = Z_sing`). -/
private theorem closedEmbeddingSingularFiltrationSectionCohomology_isZero_of_lt
    (k : ℕ) (hk : k ≤ closedEmbeddingSingularFiltrationLength i)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    -- `H^n_{Z_sing,k(ℂ)}(X(ℂ); ℚ)`, for the `k`-th stage of the singular filtration.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing,k(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing,k(ℂ)`, as a closed subset of `X(ℂ)`.
        (closedEmbeddingSingularAnalyticClosedFiltration i k))).homology n) := by
  let O (j : ℕ) := (closedEmbeddingSingularAnalyticClosedFiltration i j).compl
  have hO : Monotone O := fun _ _ hab _ hy hyb ↦
    hy (closedEmbeddingSingularAnalyticClosedFiltration_antitone i hab hyb)
  have hN : O (closedEmbeddingSingularFiltrationLength i) = ⊤ := by
    dsimp only [O]
    rw [closedEmbeddingSingularAnalyticClosedFiltration_length]
    ext y
    change (y ∉ (∅ : Set (ComplexPoint X))) ↔ y ∈ Set.univ
    simp
  exact TopCat.Sheaf.finiteNestedSupport_homology_isZero
    (TopCat.of (ComplexPoint X)) O hO (closedEmbeddingSingularFiltrationLength i) hN
    (ambientRationalInjectiveComplex X)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (fun j _ => closedEmbeddingSingularLayerSectionCohomology_isZero_of_lt
      i hi j n hn) k hk

include hi in
/-- `H^n_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0` for `n < 2(p + 1)`. -/
private theorem closedEmbeddingSingularBoundarySectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    -- `H^n_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (closedEmbeddingSingularAnalyticClosedFiltration i 0))).homology n) :=
  closedEmbeddingSingularFiltrationSectionCohomology_isZero_of_lt i hi
    0 (Nat.zero_le _) n hn

include hi in
/-- `H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`. -/
theorem closedEmbeddingSingularBoundarySectionCohomology_isZero_cycleDegree :
    -- `H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (closedEmbeddingSingularAnalyticClosedFiltration i 0))).homology
      -- Degree `2p`.
      (2 * (p : ℤ))) :=
  closedEmbeddingSingularBoundarySectionCohomology_isZero_of_lt i hi _ (by omega)

include hi in
/-- `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`. -/
private theorem closedEmbeddingSingularBoundarySectionCohomology_isZero_cycleDegree_succ :
    -- `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (closedEmbeddingSingularAnalyticClosedFiltration i 0))).homology
      -- Degree `2p + 1`.
      (2 * (p : ℤ) + 1)) :=
  closedEmbeddingSingularBoundarySectionCohomology_isZero_of_lt i hi _ (by omega)

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- Every point of the singular boundary belongs to the full support. -/
private theorem closedEmbeddingSingularBoundary_le_support :
    closedEmbeddingSingularAnalyticClosedFiltration i 0 ≤
      closedEmbeddingAnalyticClosedSupport i := by
  intro y hy
  obtain ⟨z, _, hz⟩ := hy
  exact ⟨z, hz⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] in
/-- The actual complement inclusion determining the localization sequence. -/
private theorem closedEmbeddingSupportComplement_le_smoothAmbientOpen :
    (closedEmbeddingAnalyticClosedSupport i).compl ≤ closedEmbeddingSmoothSupportAmbientOpen i :=
  fun _ hy hyS ↦ hy (closedEmbeddingSingularBoundary_le_support i hyS)

/-- The restriction `Γ(X(ℂ), RΓ_{Z(ℂ)}(ℚ)) → Γ(X(ℂ) \ Z_sing(ℂ), RΓ_{Z(ℂ)}(ℚ))` of complexes of
sections. -/
def closedEmbeddingSupportSectionRestriction :
    -- Restriction `RΓ_{Z(ℂ)}(X(ℂ)) → RΓ_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ))`.
    ((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i)) ⟶
    ((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (closedEmbeddingSmoothSupportAmbientOpen i)).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i)) :=
  TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
    (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i)) (homOfLE le_top)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hi in
/-- Restriction `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) → H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)` is an isomorphism:
in the localization sequence for `Z_sing(ℂ) ⊆ Z(ℂ)`, the neighbouring terms
`H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ)` and `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ)` vanish. -/
theorem closedEmbeddingSupportSectionRestriction_homology_isIso :
    IsIso (HomologicalComplex.homologyMap (closedEmbeddingSupportSectionRestriction i) (2 * (p : ℤ))) := by
  let T := TopCat.of (ComplexPoint X)
  let h := closedEmbeddingSupportComplement_le_smoothAmbientOpen i
  let K := ambientRationalInjectiveComplex X
  let S := TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex T h ⊤ K
  let := TopCat.Sheaf.nestedSupportRestriction_homologyMap_isIso_of_vanishing T h ⊤ K
    (2 * (p : ℤ))
    (closedEmbeddingSingularBoundarySectionCohomology_isZero_cycleDegree i hi)
    (closedEmbeddingSingularBoundarySectionCohomology_isZero_cycleDegree_succ i hi)
  have he : HomologicalComplex.homologyMap S.g (2 * (p : ℤ)) ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso T h K).hom (2 * (p : ℤ)) =
    HomologicalComplex.homologyMap (closedEmbeddingSupportSectionRestriction i) (2 * (p : ℤ)) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f (2 * (p : ℤ)))
      (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso_g T h K)
  rw [← he]
  infer_instance

/-- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) ≅ H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)`: the restriction map, with its
inverse. -/
def closedEmbeddingSupportExtensionIso :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`.
    ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
        (closedEmbeddingAnalyticClosedSupport i))).homology
      -- Degree `2p`.
      (2 * (p : ℤ))) ≅
    -- `H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)`.
    ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (closedEmbeddingSmoothSupportAmbientOpen i)).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))).homology
          -- Degree `2p`.
          (2 * (p : ℤ))) :=
  letI := closedEmbeddingSupportSectionRestriction_homology_isIso i hi
  asIso (HomologicalComplex.homologyMap (closedEmbeddingSupportSectionRestriction i) (2 * (p : ℤ)))

end AlgebraicGeometry.ComplexPoint
