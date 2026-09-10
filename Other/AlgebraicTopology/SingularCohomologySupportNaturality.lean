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

public import HodgeConjecture.Lemmas.AlgebraicTopology.RelativeHomotopyInvariance

/-!
# Naturality of forgetting support in singular cohomology

The map from cohomology with support to ordinary cohomology is natural for continuous maps.
The support on the source is the inverse image of the support on the target.  This is the
chain-level compatibility needed to compare point-supported coclasses after transporting a
point by a map homotopic to the identity.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- Homotopic maps induce equal pullbacks on singular cohomology. -/
theorem cohomologyMap_eq_of_homotopy
    (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ)
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    cohomologyMap R n f = cohomologyMap R n g := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  intro z
  change α (homologyMap R n f z) = α (homologyMap R n g z)
  congr 1
  exact ConcreteCategory.congr_hom
    (H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of R R) n) z

set_option backward.isDefEq.respectTransparency false in
/-- Pullback in singular cohomology commutes with forgetting support. -/
theorem cohomologyMap_forgetSupport
    (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (Z : Set Y) (α : CohomologyWithSupport R Y Z n) :
    cohomologyMap R n f (forgetSupport R Y Z n α) =
      forgetSupport R X (f ⁻¹' Z) n
        (cohomologyWithSupportMap R n f Z α) := by
  ext z
  change α ((relativeHomologyProjection R (TopPair.ofSubset Zᶜ) n).hom
      (homologyMap R n f z)) =
    α (relativeHomologyMap R n (preimageSupportPairMap f Z)
      ((relativeHomologyProjection R
        (TopPair.ofSubset (f ⁻¹' Z)ᶜ) n).hom z))
  congr 1
  let a := preimageSupportPairMap f Z
  have hnat := TopPair.Homotopy.relativeChainProjection_naturality (R := R) a
  have hhom := congrArg (fun g ↦ HomologicalComplex.homologyMap g n) hnat
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hhom
  have happ := ConcreteCategory.congr_hom hhom z
  simp only [ModuleCat.hom_comp] at happ
  change (relativeHomologyMap R n a)
      ((relativeHomologyProjection R
        (TopPair.ofSubset (f ⁻¹' Z)ᶜ) n).hom z) =
    (relativeHomologyProjection R (TopPair.ofSubset Zᶜ) n).hom
      (homologyMap R n (TopPair.Hom.fst a) z) at happ
  have hafst : TopPair.Hom.fst a = f := rfl
  rw [hafst] at happ
  exact happ.symm

/-- Pulling a supported class back along a map homotopic to the identity does not change its
ordinary class after forgetting support. -/
theorem forgetSupport_cohomologyWithSupportMap_eq_of_homotopyToId
    (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ)
    (f : X ⟶ X) (H : TopCat.Homotopy f (𝟙 X))
    (Z : Set X) (α : CohomologyWithSupport R X Z n) :
    forgetSupport R X (f ⁻¹' Z) n
        (cohomologyWithSupportMap R n f Z α) =
      forgetSupport R X Z n α := by
  rw [← cohomologyMap_forgetSupport, cohomologyMap_eq_of_homotopy R n H, cohomologyMap_id]
  rfl

/-- If a map homotopic to the identity transports one supported class to another, the two
classes have the same image in ordinary cohomology.  The equality `hW` only identifies the
actual inverse-image support with the named source support; no equivalence of unrelated
cohomology groups is assumed. -/
theorem forgetSupport_eq_of_supportedClass_transport
    (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ)
    (f : X ⟶ X) (H : TopCat.Homotopy f (𝟙 X))
    (Z W : Set X) (hW : f ⁻¹' Z = W)
    (α : CohomologyWithSupport R X Z n)
    (β : CohomologyWithSupport R X W n)
    (hβ : LinearEquiv.cast (R := R)
      (M := fun S : Set X ↦ CohomologyWithSupport R X S n) hW
        (cohomologyWithSupportMap R n f Z α) = β) :
    forgetSupport R X W n β = forgetSupport R X Z n α := by
  subst W
  have hβ' : cohomologyWithSupportMap R n f Z α = β := by
    simpa using hβ
  rw [← hβ']
  exact forgetSupport_cohomologyWithSupportMap_eq_of_homotopyToId R X n f H Z α

end AlgebraicTopology.Singular
