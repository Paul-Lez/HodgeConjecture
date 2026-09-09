/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothDimensionFormula
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Regular local rings of smooth schemes

This file proves that local étale maps preserve regular local rings. It follows that every
localization at a prime of a standard-smooth algebra over a field is regular local. Applying this
to affine neighborhoods gives regularity of every stalk of a smooth complex scheme.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Topology

namespace IsRegularLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An essentially finite-type, formally unramified, flat, and quasi-finite local map out of a
regular local ring has regular local target. -/
lemma of_formallyUnramified_of_flat_of_quasiFinite
    [IsRegularLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] [Algebra.QuasiFinite R S] :
    IsRegularLocalRing S := by
  let : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)]
  have hspan :
      (↑(Submodule.spanFinrank ((maximalIdeal R).map (algebraMap R S))) : WithBot ℕ∞) ≤
        (↑(Submodule.spanFinrank (maximalIdeal R)) : WithBot ℕ∞) := by
    exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
      (maximalIdeal R).fg_of_isNoetherianRing
  refine hspan.trans_eq ?_
  rw [(isRegularLocalRing_iff R).mp inferInstance]
  have hheight := Algebra.QuasiFinite.height_eq_height_under
    (R := R) (S := S) (maximalIdeal S)
  rw [show (maximalIdeal S).under R = maximalIdeal R by
    exact IsLocalRing.maximalIdeal_comap (algebraMap R S)] at hheight
  calc
    ringKrullDim R = (↑(maximalIdeal R).height : WithBot ℕ∞) :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ = (↑(maximalIdeal S).height : WithBot ℕ∞) := by rw [hheight]
    _ = ringKrullDim S := IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end IsRegularLocalRing

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Every localization at a prime of an étale algebra over a regular ring is regular local. -/
lemma Etale.isRegularLocalRing_atPrime [IsRegularRing R] [Algebra.Etale R S]
    (P : Ideal S) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) := by
  let q : Ideal R := P.under R
  let : q.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  let : P.LiesOver q := ⟨rfl⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver q P
  have _ : Algebra.FormallyEtale R (Localization.AtPrime P) := inferInstance
  have _ : Algebra.FormallyEtale (Localization.AtPrime q) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.localization_base q.primeCompl
  have _ : Algebra.EssFiniteType (Localization.AtPrime q) (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_comp R _ _
  have _ : Module.Flat (Localization.AtPrime q) (Localization.AtPrime P) := inferInstance
  have _ : Algebra.QuasiFinite (Localization.AtPrime q) (Localization.AtPrime P) :=
    Algebra.QuasiFinite.of_restrictScalars R _ _
  have _ : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularRing.isRegularLocalRing_localization q
  exact IsRegularLocalRing.of_formallyUnramified_of_flat_of_quasiFinite
    (R := Localization.AtPrime q) (S := Localization.AtPrime P)

end Algebra

namespace RingHom

variable {K S : Type*} [Field K] [CommRing S]

/-- Every localization at a prime of a standard-smooth algebra over a field is regular local. -/
lemma IsStandardSmooth.isRegularLocalRing_atPrime
    {f : K →+* S} (hf : f.IsStandardSmooth) (P : Ideal S) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) := by
  obtain ⟨d, g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) K) S := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin d) K) S :=
    RingHom.etale_algebraMap.mp hg
  exact Algebra.Etale.isRegularLocalRing_atPrime
    (R := MvPolynomial (Fin d) K) P

/-- Every localization at a prime of a standard-smooth algebra over a field is regular local. -/
lemma IsStandardSmoothOfRelativeDimension.isRegularLocalRing_atPrime
    {f : K →+* S} {d : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension d)
    (P : Ideal S) [P.IsPrime] : IsRegularLocalRing (Localization.AtPrime P) := by
  exact hf.isStandardSmooth.isRegularLocalRing_atPrime P

end RingHom

namespace AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Spec ↧ℂ}

/-- Every scheme-theoretic stalk of a smooth complex scheme is a regular local ring. -/
lemma Smooth.isRegularLocalRing_stalk_complex [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, hf⟩ :=
    Smooth.exists_affine_isStandardSmooth f x
  let P : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hstandard : (complexRestrictionMap f V).IsStandardSmooth :=
    complexRestrictionMap_isStandardSmooth f hf
  have hregular : IsRegularLocalRing (Localization.AtPrime P) :=
    RingHom.IsStandardSmooth.isRegularLocalRing_atPrime hstandard P
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  exact @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime P) _ hregular
    (X.presheaf.stalk x) _
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (X.presheaf.stalk x)).toRingEquiv

variable {d : ℕ}

/-- The fixed-relative-dimension form of regularity of stalks of smooth complex schemes. -/
lemma SmoothOfRelativeDimension.isRegularLocalRing_stalk_complex
    [SmoothOfRelativeDimension d f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  exact Smooth.isRegularLocalRing_stalk_complex (f := f) x

end AlgebraicGeometry
