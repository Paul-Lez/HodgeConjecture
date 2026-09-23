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

public import Other.AlgebraicTopology.SimplicialCochainExtension
public import Other.AlgebraicTopology.Singular.Sheaf.CochainFlasque
public import Mathlib.Algebra.Module.Projective -- shake: keep
public import Mathlib.Topology.Sheaves.Flasque

import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Flasqueness of open singular cochains

Restriction of a singular cochain to an open subset is surjective: the inclusion is injective on
singular simplices, and a cochain, being an arbitrary function on singular simplices, extends by
zero on the simplices not contained in the smaller open subset. This works over any commutative
ring of coefficients. Consequently, the presheaf of singular cochains in each fixed degree is
flasque.

The extension by zero is linear. Flasqueness and the top-open identification are supplied by
the imported singular-cochain API. These statements concern the presheaf before sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- The inclusion of open subsets is an injective continuous map. -/
lemma openInclusion_injective {U V : Opens X} (i : U ⟶ V) :
    Function.Injective ((Opens.toTopCat X).map i) :=
  fun _ _ h ↦ Subtype.ext (congrArg (fun z : V ↦ z.1) h)

/-- The linear extension of cochains by zero along an inclusion of open subsets: a cochain on
the smaller open subset is extended by zero on the singular simplices not contained in it. -/
noncomputable def openSingularCochainExtensionByZero
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    OpenCochains R X V n →ₗ[R] OpenCochains R X U n :=
  TopCat.singularCochainExtension R ((Opens.toTopCat X).map i.unop) n

/-- Restricting the extension by zero recovers the original cochain. -/
lemma openSingularCochainRestriction_comp_extensionByZero
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    (((openSingularChainComplexFunctor R X).map i.unop).f n).hom.dualMap.comp
        (openSingularCochainExtensionByZero R X i n) = LinearMap.id :=
  TopCat.singularChainComplexFunctor_dualMap_comp_singularCochainExtension R
    ((Opens.toTopCat X).map i.unop) (openInclusion_injective X i.unop) n

@[simp]
lemma openSingularCochainRestriction_extensionByZero
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) (φ : OpenCochains R X V n) :
    (singularCochainPresheaf R X n).map i
        (openSingularCochainExtensionByZero R X i n φ) = φ :=
  LinearMap.congr_fun (openSingularCochainRestriction_comp_extensionByZero R X i n) φ

/-- Every cochain on an open subset extends to a cochain on the whole space. -/
lemma globalOpenSingularCochainRestriction_surjective (U : Opens X) (n : ℕ) :
    Function.Surjective
      ((singularCochainPresheaf R X n).map (homOfLE (le_top : U ≤ ⊤)).op) :=
  openSingularCochainRestriction_surjective R X _ n

end AlgebraicTopology.Singular
