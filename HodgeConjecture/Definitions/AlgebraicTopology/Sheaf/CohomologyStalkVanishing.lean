/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.HomologySection
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueQuasiIso
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Cohomology-sheaf stalk vanishing from cofinal local section calculations

For a complex of additive sheaves, the stalk of the homology presheaf of its underlying presheaf
complex is canonically the stalk of its homology sheaf. Both comparisons go through exact stalk
functors.

Consequently, vanishing of section-complex homology on a cofinal system of neighborhoods implies
vanishing of the cohomology-sheaf stalk, the neighborhood being allowed to depend on the original
open set. This is the generic passage from the local normal-slice calculation to sheaf support
purity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

open AlgebraicTopology.Singular

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an integer `n`, this presheaf sends an open `U` to `H^n(K(U))`, cycles modulo
boundaries in the complex obtained by taking sections on `U`. Its restriction maps are induced
by restriction of sections. -/
def sectionCohomologyPresheaf (n : ℤ) : Presheaf AddCommGrpCat.{u} X :=
  (((forget AddCommGrpCat.{u} X).mapHomologicalComplex ℤᵘᵖ).obj K).homology n

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an open `U` and an integer `n`, this identifies `H^n(K(U))` with the value at
`U` of the presheaf `V ↦ H^n(K(V))`. It expresses that kernels and cokernels of presheaves are
computed on each open set. -/
def sectionCohomologyPresheafOnOpenIso (n : ℤ) (U : Opens X) :
    (((supportEvaluation X U).mapHomologicalComplex ℤᵘᵖ).obj K).homology n ≅
      (sectionCohomologyPresheaf X K n).obj (op U) :=
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    ((((forget AddCommGrpCat.{u} X).mapHomologicalComplex ℤᵘᵖ).obj K).sc n)
  S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))

end TopCat.Sheaf
