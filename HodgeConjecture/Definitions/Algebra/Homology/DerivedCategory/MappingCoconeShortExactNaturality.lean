/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExact

/-! # Naturality of the canonical short-exact-sequence cone comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCocone

variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex (CochainComplex C ℤ)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `0 → A → B → C → 0` be a short exact sequence of integer-indexed cochain complexes in an
abelian category. For degrees `n` and `m = n+1`, the canonical map `A[1] → Cone(B → C)` induces
this isomorphism `H^m(A) ≅ H^n(Cone(B → C))`. -/
def shortExactHomologyIsoCone (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (n n' : ℤ) (h : 1 + n = n') :
    S.X₁.homology n' ≅ (mappingCone S.g).homology n :=
  letI : QuasiIso (shiftedLiftShortComplex S) := quasiIso_shiftedLiftShortComplex S hS
  letI : IsIso (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n) :=
    (quasiIsoAt_iff_isIso_homologyMap (shiftedLiftShortComplex S) n).mp inferInstance
  (((HomologicalComplex.homologyFunctor C ℤᵘᵖ 0).shiftIso 1 n n' h).app S.X₁).symm ≪≫
    asIso (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n)

end CochainComplex.mappingCocone
