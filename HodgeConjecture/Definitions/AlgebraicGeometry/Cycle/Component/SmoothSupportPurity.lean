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

/-- The exact analytic complement of the canonical singular boundary. -/
abbrev cycleComponentSmoothSupportAmbientOpen : Opens (ComplexPoint X) :=
  (cycleComponentSingularAnalyticClosedFiltration X x 0).compl

include hx in
/-- Actual cofinal ambient relative-cohomology calculations along the smooth locus. -/
private theorem cycleComponentSmoothSupport_exists_relativeCohomology_vanishing
    (y : ComplexPoint X) (hy : y ∈ cycleComponentSupport X x)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * p →
        IsZero (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (cycleComponentSupport X x)) n) := by
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
    i (dim X.left - p) (dim X.left) (isOpenEmbedding_map_open X O)
    hS z V hyV
  refine ⟨W, hWV, hzW, ?_⟩
  intro n hn
  exact hW n (by omega)

include hx in
/-- Cofinal supported-section vanishing for the ambient resolution. -/
private theorem cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ))
    (y : ComplexPoint X) (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex X
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hx in
/-- The restricted supported cohomology sheaves are concentrated in degree `2p`. -/
theorem cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ)) :
    IsZero (((((show Opens (TopCat.of (ComplexPoint X)) from
      cycleComponentSmoothSupportAmbientOpen X x).isOpenEmbedding.sheafPullback
        AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X
          (cycleComponentAnalyticClosedSupport X x))).homology n) := by
  let U : Opens (TopCat.of (ComplexPoint X)) := cycleComponentSmoothSupportAmbientOpen X x
  let K : CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) ℤ :=
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
  change IsZero (K.homology n)
  let : K.IsStrictlyGE 0 := by
    dsimp only [K]
    infer_instance
  exact TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    (TopCat.of (ComplexPoint X)) _ _ n
    (cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing X x hx n hn)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical lowest-degree isomorphism using the original ambient resolution and
the original ambient cohomology sheaf, both evaluated on the boundary complement. -/
def cycleComponentSmoothSupportLowestSectionCohomologyIso :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          (2 * (p : ℤ))) ≅
      ((complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)).homology
        (2 * (p : ℤ))).obj.obj (op (cycleComponentSmoothSupportAmbientOpen X x)) :=
  let U : Opens (TopCat.of (ComplexPoint X)) := cycleComponentSmoothSupportAmbientOpen X x
  let K : CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) ℤ :=
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
  letI : K.IsStrictlyGE 0 := by
    dsimp only [K]
    infer_instance
  TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso
    (TopCat.of (ComplexPoint X)) (cycleComponentSmoothSupportAmbientOpen X x)
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
    0 (2 * (p : ℤ))
    (fun j hj => cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
      X x hx j (ne_of_lt hj))
    (fun j => TopCat.Sheaf.sectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
        ((ambientRationalInjectiveComplex X).X j))

end AlgebraicGeometry.ComplexPoint
