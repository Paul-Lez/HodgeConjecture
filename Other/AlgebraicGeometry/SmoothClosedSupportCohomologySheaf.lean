/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexSupportedSingularModel
public import Other.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import Other.AlgebraicTopology.SupportedSingularSectionCohomology

/-!
# Actual cohomology-sheaf concentration for smooth closed supports

The complex is the literal supported-sections kernel applied to the fixed ambient
rational injective resolution. Its open-section homology is compared to relative
singular cohomology by the actual singular resolution and restriction-cone maps.
The constructed cofinal normal neighborhoods then imply stalkwise and sheafwise
concentration in degree twice the complex codimension.

No local purity, comparison, or orientation class is supplied to the geometric theorem.
This proves concentration, not yet the normalized identification of the surviving
cohomology sheaf with rational constants on the support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (sX : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth sX] [IsProjective sX]

local instance smoothClosedSupportCohomologySheafAnalyticTopology :
    TopologicalSpace (ComplexPoint X sX) := Point.analyticTopology

/-- The literal supported ambient rational injective complex for a closed support. -/
def complexSupportInjectiveComplex (S : Closeds (ComplexPoint X sX)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X sX))) ℤ :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside
    (TopCat.of (ComplexPoint X sX)) S.compl).mapHomologicalComplex (.up ℤ)).obj
      (ambientRationalInjectiveComplex sX)

instance complexSupportInjectiveComplex_isStrictlyGE (S : Closeds (ComplexPoint X sX)) :
    (complexSupportInjectiveComplex sX S).IsStrictlyGE 0 := by
  dsimp [complexSupportInjectiveComplex]
  infer_instance

/-- Actual open-section cohomology of the supported injective model is relative
singular cohomology of the same literal local support pair. -/
def complexSupportInjectiveSectionCohomologyEquiv (S : Closeds (ComplexPoint X sX))
    (V : Opens (ComplexPoint X sX)) (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X sX)) V).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex sX S))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (V : Set (ComplexPoint X sX)) (S : Set (ComplexPoint X sX))) n := by
  let : ∀ W : Opens (ComplexPoint X sX), ParacompactSpace W := openParacompactSpace sX
  exact (complexSupportedSingularInjectiveHomologyIso sX S.compl V (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X sX)) S S.isClosed V n)

omit [IsIntegral X] [Smooth sX] [IsProjective sX] in
/-- Negative cohomology vanishes directly from the actual nonnegative resolution. -/
theorem complexSupportInjectiveComplex_homology_isZero_negative
    (S : Closeds (ComplexPoint X sX)) (n : ℤ) (hn : n < 0) :
    IsZero ((complexSupportInjectiveComplex sX S).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((complexSupportInjectiveComplex sX S).isZero_of_isStrictlyGE 0 n hn)

omit [IsIntegral X] [Smooth sX] [IsProjective sX] in
/-- Off the support, the actual supported complex has zero cohomology stalks in every
degree: choose neighborhoods in the complement and use the defining kernel. -/
theorem complexSupportInjectiveComplex_homology_stalk_isZero_of_not_mem
    (S : Closeds (ComplexPoint X sX)) (x : ComplexPoint X sX) (hx : x ∉ S) (n : ℤ) :
    IsZero ((AlgebraicTopology.Singular.additiveSheafStalkFunctor
      (TopCat.of (ComplexPoint X sX)) x).obj
        ((complexSupportInjectiveComplex sX S).homology n)) := by
  apply TopCat.Sheaf.cohomologySheaf_stalk_isZero_of_cofinal_sections
  intro V hxV
  refine ⟨V ⊓ S.compl, inf_le_left, ⟨hxV, hx⟩, ?_⟩
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
    (TopCat.of (ComplexPoint X sX)) S.compl (V ⊓ S.compl)
    ((ambientRationalInjectiveComplex sX).X n) inf_le_right

variable {Y : Scheme} (sY : Y ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (hi : i ≫ sX = sY)
  (m d : ℕ) [SmoothOfRelativeDimension m sY] [SmoothOfRelativeDimension d sX]
  [IsClosedImmersion i]

/-- The actual closed analytic image of the smooth closed immersion. -/
def smoothClosedAnalyticSupport : Closeds (ComplexPoint X sX) :=
  ⟨Set.range (Point.map i hi), (isClosedEmbedding_map_of_closedImmersion hi).isClosed_range⟩

/-- On support points, cofinal actual normal neighborhoods prove vanishing outside
twice the complex codimension, without a local-purity hypothesis. -/
theorem smoothClosedSupportInjective_homology_stalk_isZero_of_ne
    (z : ComplexPoint Y sY) (n : ℕ) (hn : n ≠ 2 * (d - m)) :
    IsZero ((AlgebraicTopology.Singular.additiveSheafStalkFunctor
      (TopCat.of (ComplexPoint X sX)) (Point.map i hi z)).obj
        ((complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi)).homology
          (n : ℤ))) := by
  apply TopCat.Sheaf.cohomologySheaf_stalk_isZero_of_cofinal_sections
  intro V hzV
  let W := smoothClosedSupportNeighborhood sX sY i hi m d z V hzV
  refine ⟨W, smoothClosedSupportNeighborhood_le sX sY i hi m d z V hzV,
    mem_smoothClosedSupportNeighborhood sX sY i hi m d z V hzV, ?_⟩
  let : Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W : Set (ComplexPoint X sX))
        (smoothClosedAnalyticSupport sX sY i hi : Set (ComplexPoint X sX))) n) := by
    change Subsingleton (RelativeCohomology ℚ
      (smoothClosedSupportNeighborhoodPair sX sY i hi m d z V hzV) n)
    exact ModuleCat.subsingleton_of_isZero
      (smoothClosedSupportRelativeCohomology_isZero_of_ne sX sY i hi m d z V hzV n hn)
  let e := complexSupportInjectiveSectionCohomologyEquiv sX
    (smoothClosedAnalyticSupport sX sY i hi) W n
  let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X sX)) W).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi))).homology
          (n : ℤ)) := e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The actual supported cohomology sheaf vanishes in every integer degree other than
twice the complex codimension. -/
theorem smoothClosedSupportInjective_homology_isZero_of_ne (n : ℤ)
    (hn : n ≠ 2 * ((d - m : ℕ) : ℤ)) :
    IsZero ((complexSupportInjectiveComplex sX
      (smoothClosedAnalyticSupport sX sY i hi)).homology n) := by
  by_cases hneg : n < 0
  · exact complexSupportInjectiveComplex_homology_isZero_negative sX _ n hneg
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    by_cases hx : x ∈ smoothClosedAnalyticSupport sX sY i hi
    · obtain ⟨z, rfl⟩ := hx
      exact smoothClosedSupportInjective_homology_stalk_isZero_of_ne sX sY i hi m d z k
        (by exact_mod_cast hn)
    · exact complexSupportInjectiveComplex_homology_stalk_isZero_of_not_mem sX _ x hx k

/-- The proved lower support bound, packaged in Mathlib's actual cohomological grading API. -/
theorem smoothClosedSupportInjective_isGE :
    (complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi)).IsGE
      (2 * ((d - m : ℕ) : ℤ)) := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact smoothClosedSupportInjective_homology_isZero_of_ne sX sY i hi m d n (ne_of_lt hn)

/-- The proved upper support bound; together with `isGE` this is actual concentration. -/
theorem smoothClosedSupportInjective_isLE :
    (complexSupportInjectiveComplex sX (smoothClosedAnalyticSupport sX sY i hi)).IsLE
      (2 * ((d - m : ℕ) : ℤ)) := by
  rw [CochainComplex.isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact smoothClosedSupportInjective_homology_isZero_of_ne sX sY i hi m d n (ne_of_gt hn)

end AlgebraicGeometry.ComplexPoint
