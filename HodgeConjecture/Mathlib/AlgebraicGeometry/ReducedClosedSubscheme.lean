/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Reduced closed subschemes

`X.reducedClosedSubscheme S` is the reduced closed subscheme of a scheme `X` whose underlying
set is the closed subset `S`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

instance (S : Closeds X) : IsReduced (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec (.of (Γ(X, U') ⧸ I.ideal U')))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

namespace Scheme

variable (X) (S : Closeds X)

/-- The reduced closed subscheme of `X` with underlying set `S`. -/
def reducedClosedSubscheme : Scheme :=
  (IdealSheafData.vanishingIdeal S).subscheme

/-- The closed immersion of the reduced closed subscheme with underlying set `S`. -/
def reducedClosedSubschemeι : X.reducedClosedSubscheme S ⟶ X :=
  (IdealSheafData.vanishingIdeal S).subschemeι

instance : IsClosedImmersion (X.reducedClosedSubschemeι S) :=
  inferInstanceAs (IsClosedImmersion (IdealSheafData.vanishingIdeal S).subschemeι)

instance : IsReduced (X.reducedClosedSubscheme S) :=
  inferInstanceAs (IsReduced (IdealSheafData.vanishingIdeal S).subscheme)

instance [IsNoetherian X] : IsNoetherian (X.reducedClosedSubscheme S) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X.reducedClosedSubschemeι S)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X.reducedClosedSubschemeι S)

@[simp]
lemma reducedClosedSubschemeι_apply (y : X.reducedClosedSubscheme S) :
    X.reducedClosedSubschemeι S y = y.1 :=
  rfl

@[simp]
lemma range_reducedClosedSubschemeι : Set.range (X.reducedClosedSubschemeι S) = S :=
  IdealSheafData.range_subschemeι _

@[simp]
lemma ker_reducedClosedSubschemeι :
    (X.reducedClosedSubschemeι S).ker = IdealSheafData.vanishingIdeal S :=
  IdealSheafData.ker_subschemeι _

variable {S}

theorem irreducibleSpace_reducedClosedSubscheme (hS : IsIrreducible (S : Set X)) :
    IrreducibleSpace (X.reducedClosedSubscheme S) :=
  Subtype.irreducibleSpace hS

theorem isIntegral_reducedClosedSubscheme (hS : IsIrreducible (S : Set X)) :
    IsIntegral (X.reducedClosedSubscheme S) :=
  let := X.irreducibleSpace_reducedClosedSubscheme hS
  isIntegral_of_irreducibleSpace_of_isReduced _

end Scheme

end AlgebraicGeometry
