/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothClosedLift
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.OpenTransport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

/-!
# Purity along the smooth locus of a closed subvariety

The coefficient complex is the ambient injective resolution, with support in the full cycle
subvariety, restricted to the complement of the canonical singular boundary. Normal
neighborhoods of the smooth-locus closed lift show its cohomology sheaves are concentrated
in degree `2p`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

/-- The open `X(ℂ) \ Z_sing(ℂ)`, where `Z` is the closure of `x` and `Z_sing` its singular
locus. -/
abbrev closedEmbeddingSmoothSupportAmbientOpen : Opens (ComplexPoint X) :=
  -- `X(ℂ) \ Z_sing(ℂ)`.
  (closedEmbeddingSingularAnalyticClosedFiltration i 0).compl

include hi in
/-- Every `y ∈ Z(ℂ) \ Z_sing(ℂ)` has arbitrarily small open neighborhoods `W` in `X(ℂ)` with
`H^n(W, W \ Z(ℂ); ℚ) = 0` for `n ≠ 2p`. -/
private theorem closedEmbeddingSmoothSupport_exists_relativeCohomology_vanishing
    (y : ComplexPoint X) (hy : y ∈ closedEmbeddingSupport i)
    (hyU : y ∈ closedEmbeddingSmoothSupportAmbientOpen i)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * p →
        -- `H^n(W, W \ Z(ℂ); ℚ)` vanishes away from degree `2p`.
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            -- `Z(ℂ)`.
            (closedEmbeddingSupport i)) n)) := by
  let O := closedEmbeddingSmoothLocusAmbientOpen i
  let OX := closedEmbeddingSmoothLocusAmbientOpenOver i
  let S := closedEmbeddingSmoothLocusOver i
  let e : S ⟶ OX := closedEmbeddingSmoothLocusClosedLiftOver i
  let : SmoothOfRelativeDimension (dim X.left - p) S.hom := by
    change SmoothOfRelativeDimension (dim X.left - p)
      ((i.left ≫ X.hom).smoothLocus.ι ≫ Y.hom)
    rw [show Y.hom = i.left ≫ X.hom from (Over.w i).symm]
    exact closedEmbeddingSmoothLocus_smoothOfRelativeDimension i hi
  have : SmoothOfRelativeDimension (dim X.left) OX.hom := by
    change SmoothOfRelativeDimension (dim X.left) (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (dim X.left) O.ι X.hom
  let f := Point.map (openInclusion X O)
  have hS : f ⁻¹' closedEmbeddingSupport i = Set.range (Point.map e) :=
    (closedEmbeddingSmoothLocusClosedLift_complexPoints_range i).symm
  obtain ⟨w, rfl⟩ := (closedEmbeddingSmoothLocusAmbientOpen_analytic_image i).ge hyU
  obtain ⟨z, rfl⟩ := hS.le hy
  have hpd : p ≤ dim X.left := by
    have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) (closedEmbeddingGenericPoint i)
    rw [hi] at h
    exact_mod_cast h
  obtain ⟨W, hWV, hzW, hW⟩ := exists_smoothClosedSupportImageNeighborhood
    OX S e (dim X.left - p) (dim X.left) f (isOpenEmbedding_map_open X O)
    (closedEmbeddingSupport i) hS z V hyV
  refine ⟨W, hWV, hzW, ?_⟩
  intro n hn
  exact hW n (by omega)

include hi in
/-- For each `n ≠ 2p`, every `y ∈ X(ℂ) \ Z_sing(ℂ)` has arbitrarily small open neighborhoods `W`
(depending on `n`) with `H^n_{Z(ℂ)}(W; ℚ) = 0`, where `H^n_{Z(ℂ)}(W; ℚ) = H^n(Γ(W, RΓ_{Z(ℂ)}(ℚ)))`
is computed in the fixed injective resolution. -/
theorem closedEmbeddingSmoothSupport_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ))
    (y : ComplexPoint X) (hyU : y ∈ closedEmbeddingSmoothSupportAmbientOpen i)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      -- `H^n_{Z(ℂ)}(W; ℚ)` vanishes away from degree `2p`.
      IsZero ((((TopCat.Sheaf.supportEvaluation
        -- `X(ℂ)`.
        (TopCat.of (ComplexPoint X))
        -- Sections over the open `W`.
        W).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (complexSupportInjectiveComplex X
          -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
          (closedEmbeddingAnalyticClosedSupport i))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).map_isZero
      ((complexSupportInjectiveComplex X
        (closedEmbeddingAnalyticClosedSupport i)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ closedEmbeddingSupport i
    · obtain ⟨W, hWV, hyW, hW⟩ :=
        closedEmbeddingSmoothSupport_exists_relativeCohomology_vanishing i hi
          y hy hyU V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (closedEmbeddingAnalyticClosedSupport i : Set (ComplexPoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv X
        (closedEmbeddingAnalyticClosedSupport i) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
            (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))).homology
              (q : ℤ)) := e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (closedEmbeddingAnalyticClosedSupport i).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X)) (closedEmbeddingAnalyticClosedSupport i).compl W
        ((ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

/-- `RΓ_{Z(ℂ)}(ℚ)|_{X(ℂ) \ Z_sing(ℂ)}`: the `Z(ℂ)`-supported part `Γ_{Z(ℂ)}(I^•)` of the injective
resolution of `ℚ`, restricted to the open `X(ℂ) \ Z_sing(ℂ)`. -/
def closedEmbeddingSmoothRestrictedInjectiveComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (closedEmbeddingSmoothSupportAmbientOpen i))) ℤ :=
  -- `RΓ_{Z(ℂ)}(ℚ)`, restricted to the open `X(ℂ) \ Z_sing(ℂ)`.
  let U : Opens (TopCat.of (ComplexPoint X)) := closedEmbeddingSmoothSupportAmbientOpen i
  -- Restriction of sheaves to the open `U = X(ℂ) \ Z_sing(ℂ)`.
  ((U.isOpenEmbedding.sheafPullback
    AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z(ℂ)}(ℚ)` on `X(ℂ)`.
      (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance closedEmbeddingSmoothRestrictedInjectiveComplex_isStrictlyGE :
    (closedEmbeddingSmoothRestrictedInjectiveComplex i).IsStrictlyGE 0 := by
  dsimp [closedEmbeddingSmoothRestrictedInjectiveComplex]
  infer_instance

include hi in
/-- Purity: on `X(ℂ) \ Z_sing(ℂ)`, the cohomology sheaves `𝓗^n(RΓ_{Z(ℂ)}(ℚ))` vanish for
`n ≠ 2p`. -/
theorem closedEmbeddingSmoothRestrictedInjective_homology_isZero_of_ne
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ)) :
    -- The cohomology sheaf `𝓗^n(RΓ_{Z(ℂ)}(ℚ))` on `X(ℂ) \ Z_sing(ℂ)` is zero for `n ≠ 2p`.
    IsZero ((closedEmbeddingSmoothRestrictedInjectiveComplex i).homology n) :=
  TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    (TopCat.of (ComplexPoint X)) _ _ n
    (closedEmbeddingSmoothSupport_exists_supportedInjectiveSection_vanishing i hi n hn)

/-- `H^{2p}_{Z(ℂ)}(U; ℚ) ≅ Γ(U, 𝓗^{2p}(RΓ_{Z(ℂ)}(ℚ)))` for `U = X(ℂ) \ Z_sing(ℂ)`: because the
cohomology sheaves vanish below degree `2p` on `U`, the degree-`2p` cohomology of sections over
`U` is the sections of the degree-`2p` cohomology sheaf. -/
def closedEmbeddingSmoothSupportLowestSectionCohomologyIso :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)`.
    ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (closedEmbeddingSmoothSupportAmbientOpen i)).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))).homology
          -- Degree `2p`.
          (2 * (p : ℤ))) ≅
      -- Sections of the cohomology sheaf `𝓗^{2p}(RΓ_{Z(ℂ)}(ℚ))` over `X(ℂ) \ Z_sing(ℂ)`.
      ((complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i)).homology
        -- Degree `2p`.
        (2 * (p : ℤ))).obj.obj
          -- The open `X(ℂ) \ Z_sing(ℂ)`.
          (op (closedEmbeddingSmoothSupportAmbientOpen i)) :=
  TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso
    (TopCat.of (ComplexPoint X)) (closedEmbeddingSmoothSupportAmbientOpen i)
    (complexSupportInjectiveComplex X (closedEmbeddingAnalyticClosedSupport i))
    0 (2 * (p : ℤ))
    (fun j hj => closedEmbeddingSmoothRestrictedInjective_homology_isZero_of_ne
      i hi j (ne_of_lt hj))
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (closedEmbeddingAnalyticClosedSupport i).compl
        ((ambientRationalInjectiveComplex X).X j))

end AlgebraicGeometry.ComplexPoint
