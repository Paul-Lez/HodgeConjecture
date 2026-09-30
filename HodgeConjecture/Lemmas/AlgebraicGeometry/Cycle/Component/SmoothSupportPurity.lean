/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology

/-!
# Purity along the smooth locus of an integral cycle component

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- Every `y ∈ Z(ℂ) \ Z_sing(ℂ)` has arbitrarily small open neighborhoods `W` in `X(ℂ)` with
`H^n(W, W \ Z(ℂ); ℚ) = 0` for `n ≠ 2p`. -/
theorem cycleComponentSmoothSupport_exists_relativeCohomology_vanishing
    (y : ComplexPoint X) (hy : y ∈ cycleComponentSupport X x)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * p →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
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
(depending on `n`) with supported section cohomology in degree `n` equal to zero. -/
theorem cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ))
    (y : ComplexPoint X) (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportInjectiveComplex X
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
          (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
            (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
              (q : ℤ)) := e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (cycleComponentAnalyticClosedSupport X x).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl W
        ((ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

/-- The supported injective complex restricted to the smooth ambient open. -/
def cycleComponentSmoothRestrictedInjectiveComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (cycleComponentSmoothSupportAmbientOpen X x))) ℤ :=
  let U : Opens (TopCat.of (ComplexPoint X)) := cycleComponentSmoothSupportAmbientOpen X x
  ((U.isOpenEmbedding.sheafPullback
    AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance cycleComponentSmoothRestrictedInjectiveComplex_isStrictlyGE :
    (cycleComponentSmoothRestrictedInjectiveComplex X x).IsStrictlyGE 0 := by
  dsimp [cycleComponentSmoothRestrictedInjectiveComplex]
  infer_instance

include hx in
/-- Purity gives zero cohomology sheaves for the supported injective model off degree `2p`. -/
theorem cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ)) :
    IsZero ((cycleComponentSmoothRestrictedInjectiveComplex X x).homology n) :=
  TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    (TopCat.of (ComplexPoint X)) _ _ n
    (cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing X x hx n hn)

/-- The model-level lowest-degree section comparison used by legacy normalization proofs. -/
def cycleComponentSmoothSupportLowestSectionCohomologyComplexIso :
    ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          (2 * (p : ℤ))) ≅
      ((complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)).homology
        (2 * (p : ℤ))).presheaf.obj
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

/-- Its forward map displays the open-section identification, canonical
sheafification comparison on the open, and exact open-restriction homology comparison. -/
@[simp] theorem cycleComponentSmoothSupportLowestSectionCohomologyComplexIso_hom :
    (cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx).hom =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.openRestrictionTopSectionComplexIso (TopCat.of (ComplexPoint X))
          (cycleComponentSmoothSupportAmbientOpen X x)
          (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).inv
        (2 * (p : ℤ)) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection
        (TopCat.of (cycleComponentSmoothSupportAmbientOpen X x))
        (cycleComponentSmoothRestrictedInjectiveComplex X x) (2 * (p : ℤ)) ⊤ ≫
      (TopCat.Sheaf.openRestrictionHomologyTopSectionsIso (TopCat.of (ComplexPoint X))
        (cycleComponentSmoothSupportAmbientOpen X x)
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (2 * (p : ℤ))).hom := rfl

include hx in
/-- Purity gives the corresponding vanishing for the supported cohomology sheaf. -/
theorem cycleComponentSmoothSupportCohomologySheaf_isZero_of_ne
    (n : ℕ) (hn : n ≠ 2 * p) :
    IsZero (((cycleComponentSmoothSupportAmbientOpen X x).isOpenEmbedding.sheafPullback
      AddCommGrpCat).obj
      (𝓗_[cycleComponentSupport X x]^n(TopCat.of (ComplexPoint X); ℚ))) := by
  let U := cycleComponentSmoothSupportAmbientOpen X x
  let Z := cycleComponentAnalyticClosedSupport X x
  change IsZero (((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
    (𝓗_[Z]^n(TopCat.of (ComplexPoint X); ℚ))))
  let hzero : IsZero ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X Z)).homology (n : ℤ)) := by
    exact TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
      (TopCat.of (ComplexPoint X)) (complexSupportInjectiveComplex X Z) U (n : ℤ)
      (cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing X x hx
        (n : ℤ) (by exact_mod_cast hn))
  exact IsZero.of_iso
    hzero
    (complexSupportInjectiveCohomologySheafIsoRelative_restrict X Z U n).symm

end AlgebraicGeometry.ComplexPoint
