/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedSingularModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothSupport.LocalHomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularSectionCohomology

/-!
# Cohomology-sheaf concentration for smooth closed supports

The complex is the supported-sections kernel applied to the fixed ambient rational injective
resolution. Its open-section homology is compared to relative singular cohomology by the
singular resolution and restriction-cone maps, and cofinal normal neighborhoods then give
stalkwise and sheafwise concentration in degree twice the complex codimension. Identifying
the surviving cohomology sheaf with rational constants on the support is left to a later file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The literal supported ambient rational injective complex for a closed support. -/
def complexSupportInjectiveComplex (S : Closeds (ComplexPoint X)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside
    (TopCat.of (ComplexPoint X)) S.compl).mapHomologicalComplex (.up ℤ)).obj
      (ambientRationalInjectiveComplex X)

instance complexSupportInjectiveComplex_isStrictlyGE (S : Closeds (ComplexPoint X)) :
    (complexSupportInjectiveComplex X S).IsStrictlyGE 0 := by
  dsimp [complexSupportInjectiveComplex]
  infer_instance

variable (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

end AlgebraicGeometry.ComplexPoint
