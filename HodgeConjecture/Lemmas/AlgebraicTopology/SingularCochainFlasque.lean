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

public import HodgeConjecture.Lemmas.AlgebraicTopology.SingularCochainSheaf
public import Mathlib.Algebra.Module.Projective -- shake: keep
public import Mathlib.Topology.Sheaves.Flasque

import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Flasqueness of open singular cochains

Restriction of a singular cochain to an open subset is surjective: the inclusion on singular
chains is injective, and a linear functional on a subspace of a vector space extends to the whole
space. Consequently, the presheaf of singular cochains in each fixed degree is flasque.

The extension may be chosen linearly. We also identify the cochains on the top open set with the
ordinary singular cochains of the ambient space. These statements concern the presheaf before
sheafification; no claim that sheafification preserves flasqueness is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Inclusion of open subsets induces a monomorphism of singular chain complexes. -/
lemma openSingularChainComplexMap_mono {U V : Opens X} (i : U ⟶ V) :
    Mono ((openSingularChainComplexFunctor R X).map i) := by
  let : Mono ((Opens.toTopCat X).map i) :=
    (TopCat.mono_iff_injective ((Opens.toTopCat X).map i)).mpr fun x y h ↦
      Subtype.ext (congrArg (fun z : V ↦ z.1) h)
  dsimp [openSingularChainComplexFunctor]
  apply Functor.map_mono

/-- Inclusion of open subsets is injective on singular chains in every degree. -/
lemma openSingularChainMap_injective {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    Function.Injective (((openSingularChainComplexFunctor R X).map i).f n).hom := by
  let : Mono ((openSingularChainComplexFunctor R X).map i) :=
    openSingularChainComplexMap_mono R X i
  rw [← ModuleCat.mono_iff_injective]
  exact Functor.map_mono (HomologicalComplex.eval (ModuleCat R) _ n)
    ((openSingularChainComplexFunctor R X).map i)

/-- Every cochain on an open subset extends linearly to a containing open subset. -/
lemma openSingularCochainRestriction_surjective
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    Function.Surjective
      ((singularCochainPresheaf R X n).map i) :=
  LinearMap.dualMap_surjective_of_injective
    (openSingularChainMap_injective R X i.unop n)

/-- Every cochain on an open subset extends to a cochain on the whole space. -/
lemma globalOpenSingularCochainRestriction_surjective (U : Opens X) (n : ℕ) :
    Function.Surjective
      ((singularCochainPresheaf R X n).map (homOfLE (le_top : U ≤ ⊤)).op) :=
  openSingularCochainRestriction_surjective R X _ n

/-- The presheaf of singular cochains in every fixed degree is flasque. -/
instance singularCochainPresheaf_isFlasque (n : ℕ) :
    TopCat.Presheaf.IsFlasque (singularCochainPresheaf R X n) where
  epi i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact openSingularCochainRestriction_surjective R X i n

end AlgebraicTopology.Singular
