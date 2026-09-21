/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.CohomologyStalkVanishing
/-!
# Canonical cohomology-sheaf sections from local section-complex classes

Exact sheafification identifies the sheafification of the presheaf of local
section-complex cohomology with the cohomology sheaf. Composing its unit
with that identification gives the canonical local-to-sheaf class map. This
provides the target in which normalized local purity classes can be glued.

The presheaf homology is taken before sheafification, and the counit is the sheafification
counit on the original coefficient complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an integer `n`, this identifies the sheafification of `U ↦ H^n(K(U))` with
the cohomology sheaf `𝓗^n(K) = ker(d^n)/im(d^{n-1})`, where the quotient is taken in sheaves. -/
def sectionCohomologyPresheafSheafificationIso (n : ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (sectionCohomologyPresheaf X K n) ≅ K.homology n :=
  let P : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
    ((forget AddCommGrpCat.{u} X).mapHomologicalComplex ℤᵘᵖ).obj K
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := P.sc n
  let e := NatIso.mapHomologicalComplex
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit)
    ℤᵘᵖ
  (S.mapHomologyIso
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).symm ≪≫
      homologyMapIso (e.app K) n

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an integer `n`, this morphism from the presheaf `U ↦ H^n(K(U))` to the
underlying presheaf of `𝓗^n(K)` sends a class of cocycle sections to its image in the quotient
sheaf `ker(d^n)/im(d^{n-1})`. -/
def sectionCohomologyPresheafToSheaf (n : ℤ) :
    sectionCohomologyPresheaf X K n ⟶ (K.homology n).obj :=
  toSheafify (Opens.grothendieckTopology X) _ ≫
    (sectionCohomologyPresheafSheafificationIso X K n).hom.hom

/-- Let `X` be a topological space and `K` an integer-indexed cochain complex of sheaves of abelian
groups on `X`. For an open `U` and an integer `n`, this is the canonical map `H^n(K(U)) → Γ(U,
𝓗^n(K))`: a cocycle section is sent to its class in the cohomology sheaf, the sheaf quotient of
cycles by boundaries. -/
def sectionCohomologyToSheafSection (n : ℤ) (U : Opens X) :
    (((supportEvaluation X U).mapHomologicalComplex ℤᵘᵖ).obj K).homology n ⟶
      (K.homology n).presheaf.obj (op U) :=
  (sectionCohomologyPresheafOnOpenIso X K n U).hom ≫
    (sectionCohomologyPresheafToSheaf X K n).app (op U)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical presheaf-to-sheaf class map induces an isomorphism on every stalk. -/
instance sectionCohomologyPresheafToSheaf_stalk_isIso (n : ℤ) (x : X) :
    IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (sectionCohomologyPresheafToSheaf X K n)) := by
  let := Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (sectionCohomologyPresheaf X K n)
  dsimp only [sectionCohomologyPresheafToSheaf]
  rw [Functor.map_comp]
  infer_instance

end TopCat.Sheaf
