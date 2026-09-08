/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import HodgeConjecture.Other.AlgebraicGeometry.ClosedImmersionSourceOpen
public import HodgeConjecture.Other.AlgebraicTopology.NeighborhoodSupportPairImage

/-!
# Actual local purity neighborhoods transported out of ambient opens

The normal-neighborhood construction requires smooth geometry but no projectivity.
This module transports its literal support pairs along an open embedding, allowing
cohomology to continue to be computed using a resolution on the original ambient
space. The support-membership identity is purely topological; no local cohomology
or purity statement is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme}
  (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ sX = sY) (m d : ℕ)
  [SmoothOfRelativeDimension m sY] [SmoothOfRelativeDimension d sX]
  [IsClosedImmersion i]

/-- Actual normal neighborhoods can be computed in any smooth auxiliary ambient open
and then transported to the original topological ambient space. -/
theorem exists_smoothClosedSupportImageNeighborhood
    {M : Type} [TopologicalSpace M]
    (f : ComplexPoint X sX → M) (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i hi))
    (z : ComplexPoint Y sY) (V : Opens M) (hzV : f (Point.map i hi z) ∈ V) :
    ∃ W : Opens M, W ≤ V ∧ f (Point.map i hi z) ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set M) S) n)) := by
  let V' : Opens (ComplexPoint X sX) := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
  let W' := smoothClosedSupportNeighborhood sX sY i hi m d z V' hzV
  let W : Opens M := ⟨f '' (W' : Set (ComplexPoint X sX)), hf.isOpenMap _ W'.isOpen⟩
  refine ⟨W, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact smoothClosedSupportNeighborhood_le sX sY i hi m d z V' hzV hw
  · exact ⟨_, mem_smoothClosedSupportNeighborhood sX sY i hi m d z V' hzV, rfl⟩
  · intro n hn
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W' : Set (ComplexPoint X sX))
          (Set.range (Point.map i hi))) n) :=
      ModuleCat.subsingleton_of_isZero
        (smoothClosedSupportRelativeCohomology_isZero_of_ne sX sY i hi m d z V' hzV n hn)
    let e := neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W'
      (Set.range (Point.map i hi)) S (fun w _ => by
        rw [← hS]
        rfl) n
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set M) S) n) := e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

omit [SmoothOfRelativeDimension m sY] in
/-- Fixed-dimensional source opens suffice: the target is restricted by deleting the
discarded closed image, while the resulting neighborhoods and pairs live in the original
ambient analytic space. No projectivity or global source dimension is needed. -/
theorem exists_smoothClosedSourceOpenNeighborhood
    (A : Y.Opens) [SmoothOfRelativeDimension m (A.ι ≫ sY)]
    (z : ComplexPoint A (A.ι ≫ sY))
    (V : Opens (ComplexPoint X sX))
    (hzV : Point.map (A.ι ≫ i) (by rw [Category.assoc, hi]) z ∈ V) :
    ∃ W : Opens (ComplexPoint X sX), W ≤ V ∧
      Point.map (A.ι ≫ i) (by rw [Category.assoc, hi]) z ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X sX))
            (Set.range (Point.map i hi))) n)) := by
  let : Smooth sX := SmoothOfRelativeDimension.smooth d sX
  let T := closedImmersionSourceOpenTarget i A
  let j := closedImmersionSourceOpenLift i A
  have hj : j ≫ (T.ι ≫ sX) = A.ι ≫ sY := by
    rw [← Category.assoc, closedImmersionSourceOpenLift_ι, Category.assoc, hi]
  let : SmoothOfRelativeDimension d (T.ι ≫ sX) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d T.ι sX
  let f := Point.map T.ι (structureMap := T.ι ≫ sX) rfl
  have hS : f ⁻¹' Set.range (Point.map i hi) = Set.range (Point.map j hj) := by
    rw [range_map_of_isImmersion_of_comm sX sY i hi,
      range_map_of_isImmersion_of_comm (T.ι ≫ sX) (A.ι ≫ sY) j hj,
      range_closedImmersionSourceOpenLift]
    rfl
  have he : f (Point.map j hj z) =
      Point.map (A.ι ≫ i) (by rw [Category.assoc, hi]) z := by
    apply Subtype.ext
    change (z.1 ≫ j) ≫ T.ι = z.1 ≫ (A.ι ≫ i)
    rw [Category.assoc, closedImmersionSourceOpenLift_ι]
  obtain ⟨W, hWV, hzW, hW⟩ := exists_smoothClosedSupportImageNeighborhood
    (T.ι ≫ sX) (A.ι ≫ sY) j hj m d f
    (isOpenEmbedding_map_open T sX) (Set.range (Point.map i hi)) hS z V (he ▸ hzV)
  exact ⟨W, hWV, he ▸ hzW, hW⟩

omit [SmoothOfRelativeDimension m sY] in
/-- The fixed-dimensional source-open calculation, transported through a further actual
open embedding. This is the form used by successive closed supports in a larger ambient. -/
theorem exists_smoothClosedSourceOpenImageNeighborhood
    {M : Type} [TopologicalSpace M]
    (f : ComplexPoint X sX → M) (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i hi))
    (A : Y.Opens) [SmoothOfRelativeDimension m (A.ι ≫ sY)]
    (z : ComplexPoint A (A.ι ≫ sY))
    (V : Opens M)
    (hzV : f (Point.map (A.ι ≫ i) (by rw [Category.assoc, hi]) z) ∈ V) :
    ∃ W : Opens M, W ≤ V ∧
      f (Point.map (A.ι ≫ i) (by rw [Category.assoc, hi]) z) ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set M) S) n)) := by
  let V' : Opens (ComplexPoint X sX) := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
  obtain ⟨W', hW'V', hzW', hW'⟩ := exists_smoothClosedSourceOpenNeighborhood
    sX sY i hi m d A z V' hzV
  let W : Opens M := ⟨f '' (W' : Set (ComplexPoint X sX)), hf.isOpenMap _ W'.isOpen⟩
  refine ⟨W, ?_, ⟨_, hzW', rfl⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hW'V' hw
  · intro n hn
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W' : Set (ComplexPoint X sX))
          (Set.range (Point.map i hi))) n) := ModuleCat.subsingleton_of_isZero (hW' n hn)
    let e := neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W'
      (Set.range (Point.map i hi)) S (fun w _ => by rw [← hS]; rfl) n
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set M) S) n) := e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.ComplexPoint
