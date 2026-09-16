/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedSingularModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.LocalHomology
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

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- `RΓ_S(ℚ)` for a closed `S ⊆ X(ℂ)`: the complex of sheaves `Γ_S(I^•)` of sections supported
on `S` of the fixed injective resolution `ℚ → I^•` on `X(ℂ)`. -/
def complexSupportInjectiveComplex (S : Closeds (ComplexPoint X)) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  -- `RΓ_S(ℚ)`: the `S`-supported subsheaves of an injective resolution of `ℚ` on `X(ℂ)`.
  ((TopCat.Sheaf.sheafSectionsSupportedOutside
    -- `X(ℂ)`.
    (TopCat.of (ComplexPoint X))
    -- The open `X(ℂ) \ S`; sections supported outside it are the sections supported on `S`.
    S.compl).mapHomologicalComplex ℤᵘᵖ).obj
      -- The injective resolution `I^•` of `ℚ` on `X(ℂ)`.
      (ambientRationalInjectiveComplex X)

instance complexSupportInjectiveComplex_isStrictlyGE (S : Closeds (ComplexPoint X)) :
    (complexSupportInjectiveComplex X S).IsStrictlyGE 0 := by
  dsimp [complexSupportInjectiveComplex]
  infer_instance

end AlgebraicGeometry.ComplexPoint
