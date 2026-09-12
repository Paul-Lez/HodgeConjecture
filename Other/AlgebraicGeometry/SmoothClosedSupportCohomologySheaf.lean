/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothSupport.CohomologySheaf
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothSupport.CohomologySheaf

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
open AlgebraicTopology.Singular

@[expose] public noncomputable section

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

variable (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

def smoothClosedAnalyticSupport : Closeds (ComplexPoint X) :=
  ⟨Set.range (Point.map i), (isClosedEmbedding_map_of_closedImmersion i).isClosed_range⟩


theorem smoothClosedSupportInjective_homology_stalk_isZero_of_ne
    (z : ComplexPoint Y) (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero ((AlgebraicTopology.Singular.additiveSheafStalkFunctor
      (TopCat.of (ComplexPoint X)) (Point.map i z)).obj
        ((complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)).homology
          (n : ℤ))) := by
  apply TopCat.Sheaf.cohomologySheaf_stalk_isZero_of_cofinal_sections
  intro V hzV
  let W := smoothClosedSupportNeighborhood X Y i m d z V hzV
  refine ⟨W, smoothClosedSupportNeighborhood_le X Y i m d z V hzV,
    mem_smoothClosedSupportNeighborhood X Y i m d z V hzV, ?_⟩
  let : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
        (smoothClosedAnalyticSupport X Y i : Set (ComplexPoint X))) n) :=
    ModuleCat.subsingleton_of_isZero
      (smoothClosedSupportRelativeCohomology_isZero_of_ne X Y i m d z V hzV n hn)
  let e := complexSupportInjectiveSectionCohomologyEquiv X
    (smoothClosedAnalyticSupport X Y i) W n
  let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i))).homology
          (n : ℤ)) := e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The actual supported cohomology sheaf vanishes in every integer degree other than
twice the complex codimension. -/
theorem smoothClosedSupportInjective_homology_isZero_of_ne (n : ℤ)
    (hn : n ≠ 2 * ((d - m : ℕ) : ℤ)) :
    IsZero ((complexSupportInjectiveComplex X
      (smoothClosedAnalyticSupport X Y i)).homology n) := by
  by_cases hneg : n < 0
  · exact complexSupportInjectiveComplex_homology_isZero_negative X _ n hneg
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    by_cases hx : x ∈ smoothClosedAnalyticSupport X Y i
    · obtain ⟨z, rfl⟩ := hx
      exact smoothClosedSupportInjective_homology_stalk_isZero_of_ne X Y i m d z k
        (by exact_mod_cast hn)
    · exact complexSupportInjectiveComplex_homology_stalk_isZero_of_not_mem X _ x hx k

/-- The proved lower support bound, packaged in Mathlib's actual cohomological grading API. -/
theorem smoothClosedSupportInjective_isGE :
    (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)).IsGE
      (2 * ((d - m : ℕ) : ℤ)) := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact smoothClosedSupportInjective_homology_isZero_of_ne X Y i m d n (ne_of_lt hn)

/-- The proved upper support bound; together with `isGE` this is actual concentration. -/
theorem smoothClosedSupportInjective_isLE :
    (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i)).IsLE
      (2 * ((d - m : ℕ) : ℤ)) := by
  rw [CochainComplex.isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact smoothClosedSupportInjective_homology_isZero_of_ne X Y i m d n (ne_of_gt hn)


end AlgebraicGeometry.ComplexPoint
