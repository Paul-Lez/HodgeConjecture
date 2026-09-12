/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenCone

/-!
# Local singular-cochain restriction cones

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenCone`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})

attribute [local instance] singularCochainOpenConeDerivedCategory

/-- Local supported cohomology in negative degrees vanishes already
termwise in this nonnegative sheaf-cochain model. The cone index is `n - 1`. -/
lemma openSingularSheafRestrictionCone_homology_isZero_negative
    {V W : Opens X} (i : W ⟶ V) (n : ℤ) (hn : n < 0) :
    IsZero ((openSingularSheafRestrictionCone R X i).homology (n - 1)) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change IsZero ((CochainComplex.mappingCone
    (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
      ComplexShape.embeddingUpNat)).X (n - 1))
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · exact (openSingularCochainSheafComplex R X V).isZero_extend_X
      ComplexShape.embeddingUpNat _ (by intro m; change (m : ℤ) ≠ n - 1 + 1; omega)
  · exact (openSingularCochainSheafComplex R X W).isZero_extend_X
      ComplexShape.embeddingUpNat _ (by intro m; change (m : ℤ) ≠ n - 1; omega)

/-- The local cone comparison preserves Mathlib's connecting morphism,
including its negative-first-projection convention. -/
@[reassoc]
lemma openRawToSingularSheafRestrictionCone_connecting {V W : Opens X} (i : W ⟶ V) :
    openRawToSingularSheafRestrictionCone R X i ≫
      (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
          ComplexShape.embeddingUpNat)).mor₃ =
    (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
          ComplexShape.embeddingUpNat)).mor₃ ≫
      (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X V)
        ComplexShape.embeddingUpNat)⟦(1 : ℤ)⟧' :=
  (CochainComplex.mappingCone.triangleMap _ _ _ _
    (openSingularSheafRestrictionInt_naturality R X i)).comm₃.symm

end AlgebraicTopology.Singular
