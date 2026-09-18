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
dimension strictly less than that of the original subvariety. Deleting the image of
the discarded source complement makes that neighborhood closed in a smaller ambient open,
and normal neighborhoods there transport to the original projective ambient space and its
fixed supported injective resolution. The local lower vanishing follows from those maps
and the dimension bounds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) (k : ℕ)

include hi in
/-- Every point in the actual `k`th layer has cofinal actual ambient neighborhoods
whose relative cohomology below degree `2(p+1)` vanishes. -/
theorem closedEmbeddingSingularLayer_exists_relativeCohomology_vanishing
    (y : ComplexPoint X)
    (hy : y ∈ closedEmbeddingSingularAnalyticClosedFiltration i k)
    (hyNext : y ∉ closedEmbeddingSingularAnalyticClosedFiltration i (k + 1))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧
      W ≤ (closedEmbeddingSingularAnalyticClosedFiltration i (k + 1)).compl ∧
      y ∈ W ∧ ∀ n : ℕ, n < 2 * (p + 1) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (closedEmbeddingSingularAnalyticClosedFiltration i k : Set (ComplexPoint X))) n)) := by
  obtain ⟨z, rfl⟩ := (closedEmbeddingSingularAnalyticClosedFiltration_layer i k).ge ⟨hy, hyNext⟩
  let O := closedEmbeddingSingularStratumAmbientOpen i k
  let OX := closedEmbeddingSingularStratumAmbientOpenOver i k
  let S := closedEmbeddingSingularFiltrationStratumOver i k
  let e : S ⟶ OX := closedEmbeddingSingularStratumClosedLiftOver i k
  obtain ⟨A, hA, hzA, m, hm, hcodim, hdim⟩ :=
    closedEmbeddingSingularFiltrationStratum_exists_smooth_relativeDimension
      i hi k z.underlying
  let : SmoothOfRelativeDimension m (openScheme S A).hom := hdim
  let zA := asOpenPoint S A z hzA
  let f := Point.map (openInclusion X O)
  have hS : f ⁻¹'
      (closedEmbeddingSingularAnalyticClosedFiltration i k : Set (ComplexPoint X)) =
        Set.range (Point.map e) :=
    (closedEmbeddingSingularStratumClosedLift_complexPoints_range i k).symm
  have he : f (Point.map (openInclusion S A ≫ e) zA) =
      Point.map (closedEmbeddingSingularFiltrationStratumOverι i k) z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A.ι ≫ closedEmbeddingSingularStratumClosedLift i k)) ≫ O.ι =
      z.left ≫ closedEmbeddingSingularFiltrationStratumι i k
    rw [Category.assoc, Category.assoc, closedEmbeddingSingularStratumClosedLift_ι,
      ← Category.assoc]
    exact congrArg (fun g => g ≫ closedEmbeddingSingularFiltrationStratumι i k)
      (liftToOpen_fac S A z hzA)
  let V' := V ⊓ (closedEmbeddingSingularAnalyticClosedFiltration i (k + 1)).compl
  have hzV' : f (Point.map (openInclusion S A ≫ e) zA) ∈ V' := by
    rw [he]
    exact ⟨hyV, hyNext⟩
  have : SmoothOfRelativeDimension (dim X.left) OX.hom := by
    change SmoothOfRelativeDimension (dim X.left) (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 (dim X.left) O.ι X.hom
  obtain ⟨W, hWV', hzW, hW⟩ := exists_smoothClosedSourceOpenImageNeighborhood
    OX S e m (dim X.left) f (isOpenEmbedding_map_open X O)
    (closedEmbeddingSingularAnalyticClosedFiltration i k : Set (ComplexPoint X))
    hS A zA V' hzV'
  exact ⟨W, hWV'.trans inf_le_left, hWV'.trans inf_le_right, he ▸ hzW,
    fun n hn ↦ hW n (by omega)⟩

include hi in
/-- The original ambient supported injective complex has cofinally vanishing section
cohomology below `2(p+1)` at every point outside the next closed support. -/
theorem closedEmbeddingSingularLayer_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1))
    (y : ComplexPoint X)
    (hyNext : y ∉ closedEmbeddingSingularAnalyticClosedFiltration i (k + 1))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
        ℤᵘᵖ).obj (complexSupportInjectiveComplex X
          (closedEmbeddingSingularAnalyticClosedFiltration i k))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).map_isZero
      ((complexSupportInjectiveComplex X
        (closedEmbeddingSingularAnalyticClosedFiltration i k)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ closedEmbeddingSingularAnalyticClosedFiltration i k
    · obtain ⟨W, hWV, _, hyW, hW⟩ :=
        closedEmbeddingSingularLayer_exists_relativeCohomology_vanishing i hi k
          y hy hyNext V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (closedEmbeddingSingularAnalyticClosedFiltration i k : Set (ComplexPoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv X
        (closedEmbeddingSingularAnalyticClosedFiltration i k) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex ℤᵘᵖ).obj
            (complexSupportInjectiveComplex X
              (closedEmbeddingSingularAnalyticClosedFiltration i k))).homology (q : ℤ)) :=
        e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (closedEmbeddingSingularAnalyticClosedFiltration i k).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X))
        (closedEmbeddingSingularAnalyticClosedFiltration i k).compl W
        ((ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

include hi in
/-- The exact open-layer section complex needed by finite support localization has
zero cohomology below `2(p+1)`. The resolution remains the one on the original
projective ambient variety; no injective resolution on a projective auxiliary open
is assumed. -/
theorem closedEmbeddingSingularLayerSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (closedEmbeddingSingularAnalyticClosedFiltration i (k + 1)).compl).mapHomologicalComplex
        ℤᵘᵖ).obj (complexSupportInjectiveComplex X
          (closedEmbeddingSingularAnalyticClosedFiltration i k))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · exact fun j ↦ TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X))
      (closedEmbeddingSingularAnalyticClosedFiltration i k).compl
      ((ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V hyV ↦
      closedEmbeddingSingularLayer_exists_supportedInjectiveSection_vanishing
        i hi k j (hj.trans_lt hn) y hy V hyV

end AlgebraicGeometry.ComplexPoint
