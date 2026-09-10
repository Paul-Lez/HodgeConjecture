/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.Algebra.Homology.MapExtend
public import HodgeConjecture.Definitions.AlgebraicGeometry.BettiGlobalSectionsComparison

/-! # Agreement of the canonical and original Betti extension comparisons -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] {I J : Type v} {c : ComplexShape I} {c' : ComplexShape J}
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]

omit [e.IsRelIff] in
/-- Both constructed extension comparisons are identity on retained terms and
the unique map between zero objects on inserted terms, so they agree exactly. -/
theorem mapExtendCanonicalIso_eq_bettiMapExtendIso :
    mapExtendCanonicalIso F K e = mapExtendIso F K e := by
  apply Iso.ext
  ext j
  change (mapExtendCanonicalXIso F K (e.r j)).hom = (mapExtendXIsoAux F K (e.r j)).hom
  cases hr : e.r j with
  | none => exact (F.map_isZero (CategoryTheory.Limits.isZero_zero C)).eq_of_src _ _
  | some i => rfl

end HomologicalComplex
