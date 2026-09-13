/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothSupport.CohomologySheaf

/-!
# Actual cohomology-sheaf concentration for smooth closed supports

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothSupport.CohomologySheaf`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Actual open-section cohomology of the supported injective model is relative
singular cohomology of the same literal local support pair. -/
def complexSupportInjectiveSectionCohomologyEquiv (S : Closeds (ComplexPoint X))
    (V : Opens (ComplexPoint X)) (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X S))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (neighborhoodSupportComplementPair
          (V : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) n := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  exact (complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)).symm.addCommGroupIsoToAddEquiv
    |>.trans (supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) S S.isClosed V n)

variable (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Negative cohomology vanishes directly from the actual nonnegative resolution. -/
theorem complexSupportInjectiveComplex_homology_isZero_negative
    (S : Closeds (ComplexPoint X)) (n : ℤ) (hn : n < 0) :
    IsZero ((complexSupportInjectiveComplex X S).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((complexSupportInjectiveComplex X S).isZero_of_isStrictlyGE 0 n hn)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Off the support, the actual supported complex has zero cohomology stalks in every
degree: choose neighborhoods in the complement and use the defining kernel. -/
theorem complexSupportInjectiveComplex_homology_stalk_isZero_of_not_mem
    (S : Closeds (ComplexPoint X)) (x : ComplexPoint X) (hx : x ∉ S) (n : ℤ) :
    IsZero ((AlgebraicTopology.Singular.additiveSheafStalkFunctor
      (TopCat.of (ComplexPoint X)) x).obj
        ((complexSupportInjectiveComplex X S).homology n)) := by
  apply TopCat.Sheaf.cohomologySheaf_stalk_isZero_of_cofinal_sections
  intro V hxV
  refine ⟨V ⊓ S.compl, inf_le_left, ⟨hxV, hx⟩, ?_⟩
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    (TopCat.Sheaf.supportedOutsideSections_isZero_of_le
      (TopCat.of (ComplexPoint X)) S.compl (V ⊓ S.compl)
      ((ambientRationalInjectiveComplex X).X n) inf_le_right)

variable (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

end AlgebraicGeometry.ComplexPoint
