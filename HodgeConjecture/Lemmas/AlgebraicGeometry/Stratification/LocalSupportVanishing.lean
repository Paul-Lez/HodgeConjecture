/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SingularClosedFiltration
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.OpenTransport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Transport.CohomologySheaf
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestrictedVanishing

/-!
# Local support vanishing on canonical singular-filtration layers

Every point of a smooth layer has a fixed-dimensional affine source neighborhood, of
dimension strictly less than that of the original cycle component. Deleting the image of
the discarded source complement makes that neighborhood closed in a smaller ambient open,
and normal neighborhoods there transport to the original projective ambient space and its
fixed supported injective resolution. The local lower vanishing follows from those maps
and the dimension bounds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open CycleComponent

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p) (k : ℕ)

include hx in
/-- Every point in the actual `k`th layer has cofinal actual ambient neighborhoods
whose relative cohomology below degree `2(p+1)` vanishes. -/
theorem cycleComponentSingularLayer_exists_relativeCohomology_vanishing
    (y : ComplexPoint X)
    (hy : y ∈ x‾ˢⁱⁿᵍ[k](ℂ))
    (hyNext : y ∉ x‾ˢⁱⁿᵍ[(k + 1)](ℂ))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧
      W ≤ (x‾ˢⁱⁿᵍ[(k + 1)](ℂ)).compl ∧
      y ∈ W ∧ ∀ n : ℕ, n < 2 * (p + 1) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (x‾ˢⁱⁿᵍ[k](ℂ) : Set (ComplexPoint X))) n)) := by
  obtain ⟨z, rfl⟩ := (analyticSingularFiltration_layer X x k).ge ⟨hy, hyNext⟩
  let O := stratumAmbientOpen X x k
  let OX := stratumAmbientOpenOver X x k
  let Y := stratumOver X x k
  let i : Y ⟶ OX := stratumClosedLiftOver X x k
  obtain ⟨A, hA, hzA, m, hm, hcodim, hdim⟩ :=
    stratum_exists_smooth_relativeDimension
      X x hx k z.underlying
  let : SmoothOfRelativeDimension m (openScheme Y A).hom := hdim
  let zA := asOpenPoint Y A z hzA
  let f := Point.map (openInclusion X O)
  have hS : f ⁻¹'
      (x‾ˢⁱⁿᵍ[k](ℂ) : Set (ComplexPoint X)) =
        Set.range (Point.map i) :=
    (range_map_stratumClosedLiftOver X x k).symm
  have he : f (Point.map (openInclusion Y A ≫ i) zA) =
      Point.map (stratumOverι X x k) z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A.ι ≫ stratumClosedLift X x k)) ≫ O.ι =
      z.left ≫ stratumι X x k
    rw [Category.assoc, Category.assoc, stratumClosedLift_ι,
      ← Category.assoc]
    exact congrArg (fun g => g ≫ stratumι X x k)
      (liftToOpen_fac Y A z hzA)
  let V' := V ⊓ (x‾ˢⁱⁿᵍ[(k + 1)](ℂ)).compl
  have hzV' : f (Point.map (openInclusion Y A ≫ i) zA) ∈ V' := by
    rw [he]
    exact ⟨hyV, hyNext⟩
  have : SmoothOfRelativeDimension (dim X.left) OX.hom := by
    change SmoothOfRelativeDimension (dim X.left) (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (dim X.left) O.ι X.hom
  obtain ⟨W, hWV', hzW, hW⟩ := exists_smoothClosedSourceOpenImageNeighborhood
    OX Y i m (dim X.left) f (isOpenEmbedding_map_open X O)
    (x‾ˢⁱⁿᵍ[k](ℂ) : Set (ComplexPoint X))
    hS A zA V' hzV'
  exact ⟨W, hWV'.trans inf_le_left, hWV'.trans inf_le_right, he ▸ hzW,
    fun n hn ↦ hW n (by omega)⟩

include hx in
/-- The original ambient supported injective complex has cofinally vanishing section
cohomology below `2(p+1)` at every point outside the next closed support. -/
theorem cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1))
    (y : ComplexPoint X)
    (hyNext : y ∉ x‾ˢⁱⁿᵍ[(k + 1)](ℂ))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
        ℤᵘᵖ).obj (complexSupportInjectiveComplex X
          (x‾ˢⁱⁿᵍ[k](ℂ)))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).map_isZero
      ((complexSupportInjectiveComplex X
        (x‾ˢⁱⁿᵍ[k](ℂ))).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ x‾ˢⁱⁿᵍ[k](ℂ)
    · obtain ⟨W, hWV, _, hyW, hW⟩ :=
        cycleComponentSingularLayer_exists_relativeCohomology_vanishing X x hx k
          y hy hyNext V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (x‾ˢⁱⁿᵍ[k](ℂ) : Set (ComplexPoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv X
        (x‾ˢⁱⁿᵍ[k](ℂ)) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
            (complexSupportInjectiveComplex X
              (x‾ˢⁱⁿᵍ[k](ℂ)))).homology (q : ℤ)) :=
        e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (x‾ˢⁱⁿᵍ[k](ℂ)).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X))
        (x‾ˢⁱⁿᵍ[k](ℂ)).compl W
        ((ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

include hx in
/-- The exact open-layer section complex needed by finite support localization has
zero cohomology below `2(p+1)`. The resolution remains the one on the original
projective ambient variety; no injective resolution on a projective auxiliary open
is assumed. -/
theorem cycleComponentSingularLayerSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (x‾ˢⁱⁿᵍ[(k + 1)](ℂ)).compl).mapHomologicalComplex
        ℤᵘᵖ).obj (complexSupportInjectiveComplex X
          (x‾ˢⁱⁿᵍ[k](ℂ)))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · exact fun j ↦ TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X))
      (x‾ˢⁱⁿᵍ[k](ℂ)).compl
      ((ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V hyV ↦
      cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
        X x hx k j (hj.trans_lt hn) y hy V hyV

end AlgebraicGeometry.ComplexPoint
