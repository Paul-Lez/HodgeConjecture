/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Reduced closed subschemes

We construct the reduced closed subscheme structure on a closed subset `S` of a scheme `X` as the
closed subscheme of the vanishing ideal sheaf of `S`.

## Main definitions

* `AlgebraicGeometry.Scheme.reducedClosedSubscheme`: the reduced closed subscheme of `X` with
  underlying set `S`.
* `AlgebraicGeometry.Scheme.reducedClosedSubschemeι`: the closed immersion
  `X.reducedClosedSubscheme S ⟶ X`.

## Main results

* `AlgebraicGeometry.Scheme.isIntegral_reducedClosedSubscheme`: if `S` is irreducible, then
  `X.reducedClosedSubscheme S` is integral.
-/

@[expose] public noncomputable section

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

instance (S : Closeds X) : IsReduced (Scheme.IdealSheafData.vanishingIdeal S).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  -- the chart at `U` is `Spec (Γ(X, U) ⧸ I.ideal U)`, and `I.ideal U` is a radical ideal
  exact (affine_isReduced_iff _).mpr <| (Ideal.isRadical_iff_quotient_reduced _).mp <|
    PrimeSpectrum.isRadical_vanishingIdeal _

/-- A closed subscheme of a Noetherian scheme is Noetherian. -/
theorem isNoetherian_of_isClosedImmersion {Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    [IsNoetherian X] : IsNoetherian Y where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f

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

instance [IsNoetherian X] : IsNoetherian (X.reducedClosedSubscheme S) :=
  isNoetherian_of_isClosedImmersion (X.reducedClosedSubschemeι S)

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

/-- The reduced closed subscheme of an irreducible closed subset is an irreducible space. -/
theorem irreducibleSpace_reducedClosedSubscheme (hS : IsIrreducible (S : Set X)) :
    IrreducibleSpace (X.reducedClosedSubscheme S) :=
  Subtype.irreducibleSpace hS

/-- The reduced closed subscheme of an irreducible closed subset is an integral scheme. -/
theorem isIntegral_reducedClosedSubscheme (hS : IsIrreducible (S : Set X)) :
    IsIntegral (X.reducedClosedSubscheme S) :=
  have := X.irreducibleSpace_reducedClosedSubscheme hS
  isIntegral_of_irreducibleSpace_of_isReduced _

end Scheme

end AlgebraicGeometry
