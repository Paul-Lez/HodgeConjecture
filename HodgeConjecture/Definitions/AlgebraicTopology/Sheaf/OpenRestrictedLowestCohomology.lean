/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestrictedVanishing

/-!
# Canonical lowest-degree section comparison on an ambient open

The coefficient complex stays on the original ambient space. The open
restriction, its exact homology comparison, and equality of the top open's
image identify the lowest-degree comparison on the restricted space with an
isomorphism between ambient section cohomology and ambient cohomology-sheaf sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- Let `X` be a topological space and `U ⊆ X` open. For each sheaf of abelian groups `F` on `X`,
global sections of `F|_U` are exactly sections of `F` over `U`. This is the resulting natural
isomorphism `Γ(U, F|_U) ≅ F(U)`. -/
def openRestrictionTopSectionsIso :
    U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} ⋙ supportEvaluation (TopCat.of U) ⊤ ≅
      supportEvaluation X U :=
  NatIso.ofComponents (fun F => F.obj.mapIso
    (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top U))))
    (fun f => (f.hom.naturality _).symm)

variable (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an open `U`, this identifies the complex of global sections of `K|_U` with
the complex `K(U)` obtained by evaluating the original sheaves on `U`. -/
def openRestrictionTopSectionComplexIso :
    ((supportEvaluation (TopCat.of U) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        ℤᵘᵖ).obj K) ≅
      ((supportEvaluation X U).mapHomologicalComplex ℤᵘᵖ).obj K :=
  (NatIso.mapHomologicalComplex (openRestrictionTopSectionsIso X U) ℤᵘᵖ).app K

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an open `U` and an integer `n`, exactness of restriction gives `𝓗^n(K|_U) ≅
𝓗^n(K)|_U`. This is the induced isomorphism between their groups of sections on `U`. -/
def openRestrictionHomologyTopSectionsIso (n : ℤ) :
    (((((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
      ℤᵘᵖ).obj K).homology n).obj.obj (op (⊤ : Opens (TopCat.of U)))) ≅
        (K.homology n).obj.obj (op U) :=
  (supportEvaluation (TopCat.of U) ⊤).mapIso
    ((K.sc n).mapHomologyIso (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})) ≪≫
      (openRestrictionTopSectionsIso X U).app (K.homology n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. Let `U ⊆ X` be open. Suppose `K` is zero below `N`, all its terms are flasque,
and the cohomology sheaves of `K|_U` vanish below degree `n`. Then the canonical map from
classes of cocycle sections to sections of the cohomology sheaf is this isomorphism `H^n(K(U)) ≅
Γ(U, 𝓗^n(K))`. -/
def openRestrictedLowestSectionCohomologyIso (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero
      ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        ℤᵘᵖ).obj K).homology j))
    (hflasque : ∀ j, (K.X j).IsFlasque) :
    (((supportEvaluation X U).mapHomologicalComplex ℤᵘᵖ).obj K).homology n ≅
      (K.homology n).obj.obj (op U) :=
  let L := ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
    ℤᵘᵖ).obj K
  have hLF (j : ℤ) : (L.X j).IsFlasque := by
    let := hflasque j
    exact openSheafRestriction_isFlasque X U (K.X j)
  (HomologicalComplex.homologyMapIso (openRestrictionTopSectionComplexIso X U K) n).symm ≪≫
    lowestSectionCohomologyIso (TopCat.of U) L N n hK hLF ⊤ ≪≫
      openRestrictionHomologyTopSectionsIso X U K n

end TopCat.Sheaf
