/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CycleComponentSmoothClosedLift
public import Other.AlgebraicGeometry.SmoothClosedSupportOpenTransport
public import Other.AlgebraicGeometry.SmoothClosedSupportCohomologySheaf
public import Other.AlgebraicTopology.OpenRestrictedLowestCohomology
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothDimensionFormula

/-!
# Actual purity along the smooth locus of an integral cycle component

The coefficient complex is the original ambient injective resolution, with support in
the full cycle component, restricted to the complement of the canonical singular
boundary. Actual normal neighborhoods of the smooth-locus closed lift prove that its
cohomology sheaves are concentrated in degree `2p`. No projectivity of the open ambient,
local purity data, or comparison equivalence is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)
  {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p)

local instance cycleComponentSmoothSupportPurityAnalyticTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

/-- The exact analytic complement of the canonical singular boundary. -/
abbrev cycleComponentSmoothSupportAmbientOpen : Opens (ComplexPoint X s) :=
  (cycleComponentSingularAnalyticClosedFiltration s x 0).compl

include d hx in
/-- Actual cofinal ambient relative-cohomology calculations along the smooth locus. -/
theorem cycleComponentSmoothSupport_exists_relativeCohomology_vanishing
    (y : ComplexPoint X s) (hy : y ∈ cycleComponentSupport s x)
    (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen s x)
    (V : Opens (ComplexPoint X s)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X s), W ≤ V ∧ y ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * p →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X s))
            (cycleComponentSupport s x)) n)) := by
  let O := cycleComponentSmoothLocusAmbientOpen s x
  let i := cycleComponentSmoothLocusClosedLift s x
  let sY := i ≫ O.ι ≫ s
  let : SmoothOfRelativeDimension (d - p) sY := by
    dsimp [sY]
    rw [← Category.assoc, cycleComponentSmoothLocusClosedLift_ι, Category.assoc]
    exact cycleComponentSmoothLocus_smoothOfRelativeDimension s x (d := d) hx
  let f := Point.map O.ι (structureMap := O.ι ≫ s) rfl
  have hS : f ⁻¹' cycleComponentSupport s x = Set.range (Point.map i (structureMap := sY) rfl) :=
    (cycleComponentSmoothLocusClosedLift_complexPoints_range s x).symm
  obtain ⟨w, rfl⟩ := (cycleComponentSmoothLocusAmbientOpen_analytic_image s x).ge hyU
  obtain ⟨z, rfl⟩ := hS.le hy
  have hpd : p ≤ d := by
    have h := SmoothOfRelativeDimension.coheight_le_complex (f := s) (d := d) x
    rw [hx] at h
    exact_mod_cast h
  obtain ⟨W, hWV, hzW, hW⟩ := exists_smoothClosedSupportImageNeighborhood
    (O.ι ≫ s) sY i rfl (d - p) d f (isOpenEmbedding_map_open O s)
    (cycleComponentSupport s x) hS z V hyV
  refine ⟨W, hWV, hzW, ?_⟩
  intro n hn
  exact hW n (by omega)

include d hx in
/-- Cofinal supported-section vanishing for the literal original ambient resolution. -/
theorem cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ))
    (y : ComplexPoint X s) (hyU : y ∈ cycleComponentSmoothSupportAmbientOpen s x)
    (V : Opens (ComplexPoint X s)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X s), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) W).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex s
          (cycleComponentAnalyticClosedSupport s x))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) V).map_isZero
      ((complexSupportInjectiveComplex s
        (cycleComponentAnalyticClosedSupport s x)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ cycleComponentSupport s x
    · obtain ⟨W, hWV, hyW, hW⟩ :=
        cycleComponentSmoothSupport_exists_relativeCohomology_vanishing s x (d := d) hx
          y hy hyU V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X s))
            (cycleComponentAnalyticClosedSupport s x : Set (ComplexPoint X s))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv s
        (cycleComponentAnalyticClosedSupport s x) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X s)) W).mapHomologicalComplex (.up ℤ)).obj
            (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))).homology
              (q : ℤ)) := e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (cycleComponentAnalyticClosedSupport s x).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X s)) (cycleComponentAnalyticClosedSupport s x).compl W
        ((ambientRationalInjectiveComplex s).X (q : ℤ)) inf_le_right

/-- Restriction of the original full-support injective model to the boundary complement. -/
def cycleComponentSmoothRestrictedInjectiveComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (cycleComponentSmoothSupportAmbientOpen s x))) ℤ := by
  let U : Opens (TopCat.of (ComplexPoint X s)) := cycleComponentSmoothSupportAmbientOpen s x
  exact ((U.isOpenEmbedding.sheafPullback
    AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))

instance cycleComponentSmoothRestrictedInjectiveComplex_isStrictlyGE :
    (cycleComponentSmoothRestrictedInjectiveComplex s x).IsStrictlyGE 0 := by
  dsimp [cycleComponentSmoothRestrictedInjectiveComplex]
  infer_instance

/-- Restricting the actual flasque supported coefficient sheaves preserves flasqueness. -/
theorem cycleComponentSmoothRestrictedInjectiveComplex_isFlasque (n : ℤ) :
    ((cycleComponentSmoothRestrictedInjectiveComplex s x).X n).IsFlasque := by
  let : ((complexSupportInjectiveComplex s
      (cycleComponentAnalyticClosedSupport s x)).X n).IsFlasque :=
    TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X s)) (cycleComponentAnalyticClosedSupport s x).compl
        ((ambientRationalInjectiveComplex s).X n)
  exact TopCat.Sheaf.openSheafRestriction_isFlasque
    (TopCat.of (ComplexPoint X s)) (cycleComponentSmoothSupportAmbientOpen s x)
      ((complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x)).X n)

include d hx in
/-- The actual restricted cohomology sheaves are concentrated in degree `2p`. -/
theorem cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    (n : ℤ) (hn : n ≠ 2 * (p : ℤ)) :
    IsZero ((cycleComponentSmoothRestrictedInjectiveComplex s x).homology n) :=
  TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    (TopCat.of (ComplexPoint X s)) _ _ n
    (cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing s x (d := d) hx n hn)

include d hx in
/-- The actual lower cohomological bound along the smooth locus. -/
theorem cycleComponentSmoothRestrictedInjective_isGE :
    (cycleComponentSmoothRestrictedInjectiveComplex s x).IsGE (2 * (p : ℤ)) := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    s x (d := d) hx n (ne_of_lt hn)

include d hx in
/-- The actual upper cohomological bound, hence concentration rather than just lower purity. -/
theorem cycleComponentSmoothRestrictedInjective_isLE :
    (cycleComponentSmoothRestrictedInjectiveComplex s x).IsLE (2 * (p : ℤ)) := by
  rw [CochainComplex.isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
    s x (d := d) hx n (ne_of_gt hn)

/-- The canonical lowest-degree isomorphism using the original ambient resolution and
the original ambient cohomology sheaf, both evaluated on the boundary complement. -/
def cycleComponentSmoothSupportLowestSectionCohomologyIso :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s))
      (cycleComponentSmoothSupportAmbientOpen s x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))).homology
          (2 * (p : ℤ))) ≅
      ((complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x)).homology
        (2 * (p : ℤ))).obj.obj (op (cycleComponentSmoothSupportAmbientOpen s x)) :=
  TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso
    (TopCat.of (ComplexPoint X s)) (cycleComponentSmoothSupportAmbientOpen s x)
    (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))
    0 (2 * (p : ℤ))
    (fun j hj => cycleComponentSmoothRestrictedInjective_homology_isZero_of_ne
      s x (d := d) hx j (ne_of_lt hj))
    (fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X s)) (cycleComponentAnalyticClosedSupport s x).compl
        ((ambientRationalInjectiveComplex s).X j))

/-- Its forward map displays the actual open-section identification, canonical
sheafification comparison on the open, and exact open-restriction homology comparison. -/
@[simp] theorem cycleComponentSmoothSupportLowestSectionCohomologyIso_hom :
    (cycleComponentSmoothSupportLowestSectionCohomologyIso s x (d := d) hx).hom =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.openRestrictionTopSectionComplexIso (TopCat.of (ComplexPoint X s))
          (cycleComponentSmoothSupportAmbientOpen s x)
          (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))).inv
        (2 * (p : ℤ)) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection
        (TopCat.of (cycleComponentSmoothSupportAmbientOpen s x))
        (cycleComponentSmoothRestrictedInjectiveComplex s x) (2 * (p : ℤ)) ⊤ ≫
      (TopCat.Sheaf.openRestrictionHomologyTopSectionsIso (TopCat.of (ComplexPoint X s))
        (cycleComponentSmoothSupportAmbientOpen s x)
        (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))
        (2 * (p : ℤ))).hom := rfl

include d hx in
/-- Actual supported section cohomology on the boundary complement vanishes below `2p`.
Higher-degree global vanishing is not inferred from sheaf concentration. -/
theorem cycleComponentSmoothSupportSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * (p : ℤ)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s))
      (cycleComponentSmoothSupportAmbientOpen s x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X s)) _ _ 0 n
  · intro j
    exact TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X s)) (cycleComponentAnalyticClosedSupport s x).compl
        ((ambientRationalInjectiveComplex s).X j)
  · intro j hj y hy V hyV
    exact cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
      s x (d := d) hx j (ne_of_lt (hj.trans_lt hn)) y hy V hyV

end AlgebraicGeometry.ComplexPoint
