/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality

/-! # Naturality of the canonical short-exact-sequence cone comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCocone

variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex (CochainComplex C ℤ)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Homology comparison induced by the canonical short-exact-sequence
lift. Its source degree is one larger than the cone degree. -/
def shortExactHomologyIsoCone (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (n n' : ℤ) (h : 1 + n = n') :
    S.X₁.homology n' ≅ (mappingCone S.g).homology n := by
  let : QuasiIso (shiftedLiftShortComplex S) := quasiIso_shiftedLiftShortComplex S hS
  let : IsIso (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n) :=
    (quasiIsoAt_iff_isIso_homologyMap (shiftedLiftShortComplex S) n).mp inferInstance
  exact (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n n' h).app S.X₁).symm ≪≫
    asIso (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n)

end CochainComplex.mappingCocone
