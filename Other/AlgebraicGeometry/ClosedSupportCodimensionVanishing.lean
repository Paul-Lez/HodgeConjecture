/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ClosedSupportSmoothFiltration
public import Other.AlgebraicGeometry.SingularFiltrationLocalSupportVanishing
public import Other.AlgebraicTopology.FiniteSheafSupportVanishing

/-!
# Vanishing of supported cohomology along a closed subset of codimension at least `q`

This is the general-codimension form of
`cycleComponentSingularBoundarySectionCohomology_isZero_of_lt`: for an arbitrary closed subset
`W` of the ambient smooth projective variety whose smooth strata have normal codimension at
least `q`, the rational cohomology of `X^an` with support in `|W|^an` vanishes in all degrees
below `2q`.

The proof is the one used for the singular boundary of a single cycle component, run on the
generic filtration of `Other/AlgebraicGeometry/ClosedSupportSmoothFiltration.lean`:

* every point of a layer has arbitrarily small ambient neighbourhoods on which the relative
  cohomology of the support pair vanishes below `2(d - m) ≥ 2q`, by the normal-neighbourhood
  purity `exists_smoothClosedSourceOpenImageNeighborhood`;
* hence the section cohomology of the supported injective model vanishes cofinally
  (`TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing`);
* hence it vanishes on the open complement of the next closed remainder, and the finite
  nested-support induction `TopCat.Sheaf.finiteNestedSupport_homology_isZero` propagates this
  along the whole filtration.

The only input is the local dimension datum `ClosedSupportStrataNormalCodimension`, which is
supplied from a codimension hypothesis on `W` in
`Other/AlgebraicGeometry/ClosedSupportCoheightDimension.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (W : Closeds X.left) (d q : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance closedSupportCodimensionVanishingAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-- The local smooth-dimension datum of the canonical strata of `W`: every point of every
stratum has an open neighbourhood in the stratum on which the stratum is smooth of relative
dimension `m` with `m + q ≤ d`, that is, of normal codimension at least `q` in the ambient
variety. -/
def ClosedSupportStrataNormalCodimension : Prop :=
  ∀ (k : ℕ) (z : closedSupportStratum X W k),
    ∃ A : (closedSupportStratum X W k).Opens, z ∈ A ∧ ∃ m : ℕ, m + q ≤ d ∧
      SmoothOfRelativeDimension m (A.ι ≫ closedSupportStratumι X W k ≫ X.hom)

variable {X W d q}

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Every point in the `k`th layer has cofinal ambient neighbourhoods whose relative
cohomology below degree `2q` vanishes. -/
theorem closedSupportLayer_exists_relativeCohomology_vanishing
    (hstr : ClosedSupportStrataNormalCodimension X W d q) (k : ℕ)
    (y : ComplexPoint X)
    (hy : y ∈ closedSupportAnalyticFiltration X W k)
    (hyNext : y ∉ closedSupportAnalyticFiltration X W (k + 1))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ U : Opens (ComplexPoint X), U ≤ V ∧
      U ≤ (closedSupportAnalyticFiltration X W (k + 1)).compl ∧
      y ∈ U ∧ ∀ n : ℕ, n < 2 * q →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (U : Set (ComplexPoint X))
            (closedSupportAnalyticFiltration X W k : Set (ComplexPoint X))) n)) := by
  obtain ⟨z, rfl⟩ := (closedSupportAnalyticFiltration_layer X W k).ge ⟨hy, hyNext⟩
  let O := closedSupportStratumAmbientOpen X W k
  let OX := closedSupportStratumAmbientOpenOver X W k
  let Y := closedSupportStratumOver X W k
  let i : Y ⟶ OX := closedSupportStratumClosedLiftOver X W k
  obtain ⟨A, hzA, m, hm, hdim⟩ := hstr k z.underlying
  let : SmoothOfRelativeDimension m (openScheme Y A).hom := hdim
  let zA := asOpenPoint Y A z hzA
  let f := Point.map (openInclusion X O)
  have hS : f ⁻¹' (closedSupportAnalyticFiltration X W k : Set (ComplexPoint X)) =
      Set.range (Point.map i) :=
    (closedSupportStratumClosedLift_complexPoints_range X W k).symm
  have he : f (Point.map (openInclusion Y A ≫ i) zA) =
      Point.map (closedSupportStratumOverι X W k) z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A.ι ≫ closedSupportStratumClosedLift X W k)) ≫ O.ι =
      z.left ≫ closedSupportStratumι X W k
    rw [Category.assoc, Category.assoc, closedSupportStratumClosedLift_ι, ← Category.assoc]
    exact congrArg (fun g => g ≫ closedSupportStratumι X W k) (liftToOpen_fac Y A z hzA)
  let V' := V ⊓ (closedSupportAnalyticFiltration X W (k + 1)).compl
  have hzV' : f (Point.map (openInclusion Y A ≫ i) zA) ∈ V' := by
    rw [he]
    exact ⟨hyV, hyNext⟩
  have : SmoothOfRelativeDimension d OX.hom := by
    change SmoothOfRelativeDimension d (O.ι ≫ X.hom)
    infer_instance
  obtain ⟨U, hUV', hzU, hU⟩ := exists_smoothClosedSourceOpenImageNeighborhood
    OX Y i m d f (isOpenEmbedding_map_open X O)
    (closedSupportAnalyticFiltration X W k : Set (ComplexPoint X))
    hS A zA V' hzV'
  exact ⟨U, hUV'.trans inf_le_left, hUV'.trans inf_le_right, he ▸ hzU,
    fun n hn => hU n (by omega)⟩

/-- The ambient supported injective complex has cofinally vanishing section cohomology below
`2q` at every point outside the next closed remainder. -/
theorem closedSupportLayer_exists_supportedInjectiveSection_vanishing
    (hstr : ClosedSupportStrataNormalCodimension X W d q) (k : ℕ)
    (n : ℤ) (hn : n < 2 * (q : ℤ))
    (y : ComplexPoint X)
    (hyNext : y ∉ closedSupportAnalyticFiltration X W (k + 1))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ U : Opens (ComplexPoint X), U ≤ V ∧ y ∈ U ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
        U).mapHomologicalComplex (.up ℤ)).obj (complexSupportInjectiveComplex X
          (closedSupportAnalyticFiltration X W k))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).map_isZero
      ((complexSupportInjectiveComplex X
        (closedSupportAnalyticFiltration X W k)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ closedSupportAnalyticFiltration X W k
    · obtain ⟨U, hUV, _, hyU, hU⟩ :=
        closedSupportLayer_exists_relativeCohomology_vanishing hstr k y hy hyNext V hyV
      refine ⟨U, hUV, hyU, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (U : Set (ComplexPoint X))
            (closedSupportAnalyticFiltration X W k : Set (ComplexPoint X))) j) :=
        ModuleCat.subsingleton_of_isZero (hU j (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv X
        (closedSupportAnalyticFiltration X W k) U j
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
            (complexSupportInjectiveComplex X
              (closedSupportAnalyticFiltration X W k))).homology (j : ℤ)) :=
        e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let U := V ⊓ (closedSupportAnalyticFiltration X W k).compl
      refine ⟨U, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X))
        (closedSupportAnalyticFiltration X W k).compl U
        ((ambientRationalInjectiveComplex X).X (j : ℤ)) inf_le_right

/-- The open-layer section complex has zero cohomology below `2q`. -/
theorem closedSupportLayerSectionCohomology_isZero_of_lt
    (hstr : ClosedSupportStrataNormalCodimension X W d q) (k : ℕ)
    (n : ℤ) (hn : n < 2 * (q : ℤ)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (closedSupportAnalyticFiltration X W (k + 1)).compl).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex X
          (closedSupportAnalyticFiltration X W k))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · exact fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X))
      (closedSupportAnalyticFiltration X W k).compl
      ((ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V hyV =>
      closedSupportLayer_exists_supportedInjectiveSection_vanishing hstr k j
        (hj.trans_lt hn) y hy V hyV

/-- **Vanishing along a closed subset of normal codimension at least `q`.** Every closed
remainder of the canonical filtration of `W` — in particular `W` itself — has vanishing
supported section-complex cohomology in every degree below `2q`. -/
theorem closedSupportFiltrationSectionCohomology_isZero_of_lt
    (hstr : ClosedSupportStrataNormalCodimension X W d q)
    (k : ℕ) (hk : k ≤ closedSupportFiltrationLength X W)
    (n : ℤ) (hn : n < 2 * (q : ℤ)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      ⊤).mapHomologicalComplex (.up ℤ)).obj (complexSupportInjectiveComplex X
        (closedSupportAnalyticFiltration X W k))).homology n) := by
  let O (j : ℕ) := (closedSupportAnalyticFiltration X W j).compl
  have hO : Monotone O := fun _ _ hab _ hy hyb =>
    hy (closedSupportAnalyticFiltration_antitone X W hab hyb)
  have hN : O (closedSupportFiltrationLength X W) = ⊤ := by
    dsimp only [O]
    rw [closedSupportAnalyticFiltration_length]
    ext y
    change (y ∉ (∅ : Set (ComplexPoint X))) ↔ y ∈ Set.univ
    simp
  exact TopCat.Sheaf.finiteNestedSupport_homology_isZero
    (TopCat.of (ComplexPoint X)) O hO (closedSupportFiltrationLength X W) hN
    (ambientRationalInjectiveComplex X)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (fun j _ => closedSupportLayerSectionCohomology_isZero_of_lt hstr j n hn) k hk

/-- The same statement for `W` itself. -/
theorem closedSupportSectionCohomology_isZero_of_lt
    (hstr : ClosedSupportStrataNormalCodimension X W d q)
    (n : ℤ) (hn : n < 2 * (q : ℤ)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      ⊤).mapHomologicalComplex (.up ℤ)).obj (complexSupportInjectiveComplex X
        (closedSupportAnalyticFiltration X W 0))).homology n) :=
  closedSupportFiltrationSectionCohomology_isZero_of_lt hstr 0 (Nat.zero_le _) n hn

end AlgebraicGeometry.ComplexPoint
