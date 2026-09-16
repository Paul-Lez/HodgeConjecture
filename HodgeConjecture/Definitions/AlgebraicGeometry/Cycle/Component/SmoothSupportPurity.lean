/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothClosedLift
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.OpenTransport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula

/-!
# Purity along the smooth locus of an integral cycle component

The coefficient complex is the ambient injective resolution, with support in the full cycle
component, restricted to the complement of the canonical singular boundary. Normal
neighborhoods of the smooth-locus closed lift show its cohomology sheaves are concentrated
in degree `2p`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- The open `X(ℂ) \ Z_sing(ℂ)`, where `Z` is the closure of `x` and `Z_sing` its singular
locus. -/
abbrev cycleComponentSmoothSupportAmbientOpen : Opens (ComplexPoint X) :=
  -- `X(ℂ) \ Z_sing(ℂ)`.
  (cycleComponentSingularAnalyticClosedFiltration X x 0).compl

include hx in
/-- Every `y ∈ Z(ℂ) \ Z_sing(ℂ)` has arbitrarily small open neighborhoods `W` in `X(ℂ)` with
`H^n(W, W \ Z(ℂ); ℚ) = 0` for `n ≠ 2p`. -/
private theorem cycleComponentSmoothSupport_exists_relativeCohomology_vanishing
    (y : ComplexPoint X) (hy : y ∈ cycleComponentSupport X x)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * p →
        -- `H^n(W, W \ Z(ℂ); ℚ)` vanishes away from degree `2p`.
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            -- `Z(ℂ)`.
            (cycleComponentSupport X x)) n)) := by
  let O := cycleComponentSmoothLocusAmbientOpen X x
  let OX := cycleComponentSmoothLocusAmbientOpenOver X x
  let Y := cycleComponentSmoothLocusOver X x
  let i : Y ⟶ OX := cycleComponentSmoothLocusClosedLiftOver X x
  let : SmoothOfRelativeDimension (dim X.left - p) Y.hom :=
    cycleComponentSmoothLocus_smoothOfRelativeDimension X x hx
  have : SmoothOfRelativeDimension (dim X.left) OX.hom := by
    change SmoothOfRelativeDimension (dim X.left) (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (dim X.left) O.ι X.hom
  let f := Point.map (openInclusion X O)
  have hS : f ⁻¹' cycleComponentSupport X x = Set.range (Point.map i) :=
    (cycleComponentSmoothLocusClosedLift_complexPoints_range X x).symm
  obtain ⟨w, rfl⟩ := (cycleComponentSmoothLocusAmbientOpen_analytic_image X x).ge hyU
  obtain ⟨z, rfl⟩ := hS.le hy
  have hpd : p ≤ dim X.left := by
    have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) x
    rw [hx] at h
    exact_mod_cast h
  obtain ⟨W, hWV, hzW, hW⟩ := exists_smoothClosedSupportImageNeighborhood
    OX Y i (dim X.left - p) (dim X.left) f (isOpenEmbedding_map_open X O)
    (cycleComponentSupport X x) hS z V hyV
  refine ⟨W, hWV, hzW, ?_⟩
  intro n hn
  exact hW n (by omega)

include hx in
/-- For each `n ≠ 2p`, every `y ∈ X(ℂ) \ Z_sing(ℂ)` has arbitrarily small open neighborhoods `W`
(depending on `n`) with `H^n_{Z(ℂ)}(W; ℚ) = 0`, where `H^n_{Z(ℂ)}(W; ℚ) = H^n(Γ(W, RΓ_{Z(ℂ)}(ℚ)))`
is computed in the fixed injective resolution. -/
theorem cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ))
    (y : ComplexPoint X) (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      -- `H^n_{Z(ℂ)}(W; ℚ)` vanishes away from degree `2p`.
      IsZero ((((TopCat.Sheaf.supportEvaluation
        -- `X(ℂ)`.
        (TopCat.of (ComplexPoint X))
        -- Sections over the open `W`.
        W).mapHomologicalComplex (.up ℤ)).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (complexSupportInjectiveComplex X
          -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
          (cycleComponentAnalyticClosedSupport X x))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).map_isZero
      ((complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ cycleComponentSupport X x
    · obtain ⟨W, hWV, hyW, hW⟩ :=
        cycleComponentSmoothSupport_exists_relativeCohomology_vanishing X x hx
          y hy hyU V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (cycleComponentAnalyticClosedSupport X x : Set (ComplexPoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv X
        (cycleComponentAnalyticClosedSupport X x) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).obj
            (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
              (q : ℤ)) := e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (cycleComponentAnalyticClosedSupport X x).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl W
        ((ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

/-- `RΓ_{Z(ℂ)}(ℚ)|_{X(ℂ) \ Z_sing(ℂ)}`: the `Z(ℂ)`-supported part `Γ_{Z(ℂ)}(I^•)` of the injective
resolution of `ℚ`, restricted to the open `X(ℂ) \ Z_sing(ℂ)`. -/
def cycleComponentSmoothRestrictedInjectiveComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (cycleComponentSmoothSupportAmbientOpen X x))) ℤ :=
  -- `RΓ_{Z(ℂ)}(ℚ)`, restricted to the open `X(ℂ) \ Z_sing(ℂ)`.
  let U : Opens (TopCat.of (ComplexPoint X)) := cycleComponentSmoothSupportAmbientOpen X x
  -- Restriction of sheaves to the open `U = X(ℂ) \ Z_sing(ℂ)`.
  ((U.isOpenEmbedding.sheafPullback
    AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      -- `RΓ_{Z(ℂ)}(ℚ)` on `X(ℂ)`.
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance cycleComponentSmoothRestrictedInjectiveComplex_isStrictlyGE :
    (cycleComponentSmoothRestrictedInjectiveComplex X x).IsStrictlyGE 0 := by
  dsimp [cycleComponentSmoothRestrictedInjectiveComplex]
  infer_instance

include hx in
/-- Purity: on `X(ℂ) \ Z_sing(ℂ)`, the cohomology sheaves `𝓗^n(RΓ_{Z(ℂ)}(ℚ))` vanish for
`n ≠ 2p`. -/
theorem cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ)) :
    -- The cohomology sheaf `𝓗^n(RΓ_{Z(ℂ)}(ℚ))` on `X(ℂ) \ Z_sing(ℂ)` is zero for `n ≠ 2p`.
    IsZero ((cycleComponentSmoothRestrictedInjectiveComplex X x).homology n) :=
  TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    (TopCat.of (ComplexPoint X)) _ _ n
    (cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing X x hx n hn)

/-- `H^{2p}_{Z(ℂ)}(U; ℚ) ≅ Γ(U, 𝓗^{2p}(RΓ_{Z(ℂ)}(ℚ)))` for `U = X(ℂ) \ Z_sing(ℂ)`: because the
cohomology sheaves vanish below degree `2p` on `U`, the degree-`2p` cohomology of sections over
`U` is the sections of the degree-`2p` cohomology sheaf. -/
def cycleComponentSmoothSupportLowestSectionCohomologyIso :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)`.
    ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          -- Degree `2p`.
          (2 * (p : ℤ))) ≅
      -- Sections of the cohomology sheaf `𝓗^{2p}(RΓ_{Z(ℂ)}(ℚ))` over `X(ℂ) \ Z_sing(ℂ)`.
      ((complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)).homology
        -- Degree `2p`.
        (2 * (p : ℤ))).obj.obj
          -- The open `X(ℂ) \ Z_sing(ℂ)`.
          (op (cycleComponentSmoothSupportAmbientOpen X x)) :=
  TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso
    (TopCat.of (ComplexPoint X)) (cycleComponentSmoothSupportAmbientOpen X x)
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
    0 (2 * (p : ℤ))
    (fun j hj => cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
      X x hx j (ne_of_lt hj))
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
        ((ambientRationalInjectiveComplex X).X j))

end AlgebraicGeometry.ComplexPoint
