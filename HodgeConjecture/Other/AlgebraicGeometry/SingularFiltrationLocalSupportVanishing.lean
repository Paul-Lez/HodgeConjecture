/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSingularClosedFiltration
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportOpenTransport
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportCohomologySheaf
public import HodgeConjecture.Other.AlgebraicTopology.OpenRestrictedCohomologyVanishing

/-!
# Actual local support vanishing on canonical singular-filtration layers

Every point of an actual smooth layer has a fixed-dimensional affine source neighborhood.
Its dimension is strictly less than that of the original cycle component. By deleting
the image of the discarded source complement, that source neighborhood is closed in
a smaller ambient open. Actual normal neighborhoods there transport to the original
projective ambient space and its fixed supported injective resolution.

The local lower vanishing used here is proved from those maps and dimension bounds;
it is not supplied as a stratification or semipurity hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)
  {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p) (k : ℕ)

local instance singularFiltrationLocalSupportVanishingAnalyticTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

include d hx in
/-- Every point in the actual `k`th layer has cofinal actual ambient neighborhoods
whose relative cohomology below degree `2(p+1)` vanishes. -/
theorem cycleComponentSingularLayer_exists_relativeCohomology_vanishing
    (y : ComplexPoint X s)
    (hy : y ∈ cycleComponentSingularAnalyticClosedFiltration s x k)
    (hyNext : y ∉ cycleComponentSingularAnalyticClosedFiltration s x (k + 1))
    (V : Opens (ComplexPoint X s)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X s), W ≤ V ∧
      W ≤ (cycleComponentSingularAnalyticClosedFiltration s x (k + 1)).compl ∧
      y ∈ W ∧ ∀ n : ℕ, n < 2 * (p + 1) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X s))
            (cycleComponentSingularAnalyticClosedFiltration s x k : Set (ComplexPoint X s))) n)) := by
  obtain ⟨z, rfl⟩ := (cycleComponentSingularAnalyticClosedFiltration_layer s x k).ge ⟨hy, hyNext⟩
  let O := cycleComponentSingularStratumAmbientOpen s x k
  let i := cycleComponentSingularStratumClosedLift s x k
  let sY := cycleComponentSingularFiltrationStratumι s x k ≫ s
  have hi : i ≫ (O.ι ≫ s) = sY := by
    rw [← Category.assoc, cycleComponentSingularStratumClosedLift_ι]
  obtain ⟨A, hA, hzA, m, hm, hcodim, hdim⟩ :=
    cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
      s x (d := d) hx k z.underlying
  let : SmoothOfRelativeDimension m (A.ι ≫ sY) := hdim
  let zA := asOpenPoint A sY z hzA
  let f := Point.map O.ι (structureMap := O.ι ≫ s) rfl
  have hS : f ⁻¹'
      (cycleComponentSingularAnalyticClosedFiltration s x k : Set (ComplexPoint X s)) =
        Set.range (Point.map i hi) := by
    rw [range_map_of_isImmersion_of_comm (O.ι ≫ s) sY i hi,
      range_cycleComponentSingularStratumClosedLift]
    rfl
  have he : f (Point.map (A.ι ≫ i) (by rw [Category.assoc, hi]) zA) =
      Point.map (cycleComponentSingularFiltrationStratumι s x k) rfl z := by
    apply Subtype.ext
    change (zA.1 ≫ (A.ι ≫ i)) ≫ O.ι = z.1 ≫ cycleComponentSingularFiltrationStratumι s x k
    rw [Category.assoc, Category.assoc, cycleComponentSingularStratumClosedLift_ι,
      ← Category.assoc]
    exact congrArg (fun g => g ≫ cycleComponentSingularFiltrationStratumι s x k)
      (liftToOpen_fac A sY z hzA)
  let V' := V ⊓ (cycleComponentSingularAnalyticClosedFiltration s x (k + 1)).compl
  have hzV' : f (Point.map (A.ι ≫ i) (by rw [Category.assoc, hi]) zA) ∈ V' := by
    rw [he]
    exact ⟨hyV, hyNext⟩
  obtain ⟨W, hWV', hzW, hW⟩ := exists_smoothClosedSourceOpenImageNeighborhood
    (O.ι ≫ s) sY i hi m d f (isOpenEmbedding_map_open O s)
    (cycleComponentSingularAnalyticClosedFiltration s x k : Set (ComplexPoint X s))
    hS A zA V' hzV'
  refine ⟨W, hWV'.trans inf_le_left, hWV'.trans inf_le_right, he ▸ hzW, ?_⟩
  intro n hn
  exact hW n (by omega)

include d hx in
/-- The original ambient supported injective complex has cofinally vanishing section
cohomology below `2(p+1)` at every point outside the next closed support. -/
theorem cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1))
    (y : ComplexPoint X s)
    (hyNext : y ∉ cycleComponentSingularAnalyticClosedFiltration s x (k + 1))
    (V : Opens (ComplexPoint X s)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X s), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) W).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex s
          (cycleComponentSingularAnalyticClosedFiltration s x k))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) V).map_isZero
      ((complexSupportInjectiveComplex s
        (cycleComponentSingularAnalyticClosedFiltration s x k)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ cycleComponentSingularAnalyticClosedFiltration s x k
    · obtain ⟨W, hWV, _, hyW, hW⟩ :=
        cycleComponentSingularLayer_exists_relativeCohomology_vanishing s x (d := d) hx k
          y hy hyNext V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X s))
            (cycleComponentSingularAnalyticClosedFiltration s x k : Set (ComplexPoint X s))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv s
        (cycleComponentSingularAnalyticClosedFiltration s x k) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X s)) W).mapHomologicalComplex (.up ℤ)).obj
            (complexSupportInjectiveComplex s
              (cycleComponentSingularAnalyticClosedFiltration s x k))).homology (q : ℤ)) :=
        e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (cycleComponentSingularAnalyticClosedFiltration s x k).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X s))
        (cycleComponentSingularAnalyticClosedFiltration s x k).compl W
        ((ambientRationalInjectiveComplex s).X (q : ℤ)) inf_le_right

include d hx in
/-- The exact open-layer section complex needed by finite support localization has
zero cohomology below `2(p+1)`. The resolution remains the one on the original
projective ambient variety; no injective resolution on a projective auxiliary open
is assumed. -/
theorem cycleComponentSingularLayerSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s))
      (cycleComponentSingularAnalyticClosedFiltration s x (k + 1)).compl).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex s
          (cycleComponentSingularAnalyticClosedFiltration s x k))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X s)) _ _ 0 n
  · intro j
    exact TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X s))
      (cycleComponentSingularAnalyticClosedFiltration s x k).compl
      ((ambientRationalInjectiveComplex s).X j)
  · intro j hj y hy V hyV
    exact cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
      s x (d := d) hx k j (hj.trans_lt hn) y hy V hyV

end AlgebraicGeometry.ComplexPoint
