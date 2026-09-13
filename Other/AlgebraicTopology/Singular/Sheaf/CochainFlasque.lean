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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainFlasque

open CategoryTheory Limits TopologicalSpace

@[expose] public noncomputable section

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- A linear choice of extension of cochains along an inclusion of open subsets. -/
noncomputable def openSingularCochainExtension
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    OpenCochains R X V n →ₗ[R] OpenCochains R X U n :=
  Classical.choose <| LinearMap.exists_rightInverse_of_surjective
    (((openSingularChainComplexFunctor R X).map i.unop).f n).hom.dualMap
    (LinearMap.range_eq_top.mpr <| openSingularCochainRestriction_surjective R X i n)

/-- Restricting a chosen extension recovers the original cochain. -/
lemma openSingularCochainRestriction_comp_extension
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    (((openSingularChainComplexFunctor R X).map i.unop).f n).hom.dualMap.comp
        (openSingularCochainExtension R X i n) = LinearMap.id :=
  Classical.choose_spec <| LinearMap.exists_rightInverse_of_surjective
    (((openSingularChainComplexFunctor R X).map i.unop).f n).hom.dualMap
    (LinearMap.range_eq_top.mpr <| openSingularCochainRestriction_surjective R X i n)

@[simp]
lemma openSingularCochainRestriction_extension
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) (φ : OpenCochains R X V n) :
    (singularCochainPresheaf R X n).map i
        (openSingularCochainExtension R X i n φ) = φ :=
  LinearMap.congr_fun (openSingularCochainRestriction_comp_extension R X i n) φ
/-- Cochains on the top open subset are linearly equivalent to cochains on the ambient space. -/
noncomputable def singularCochainsEquivTopOpen (n : ℕ) :
    Module.Dual R
      ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj X).X n) ≃ₗ[R] OpenCochains R X (.op ⊤) n :=
  ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n).mapIso
    (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapIso
      (Opens.inclusionTopIso X))).toLinearEquiv.dualMap

/-- The top-open identification intertwines the ordinary and open singular coboundaries. -/
lemma singularCochainsEquivTopOpen_coboundary (n : ℕ) (φ : Module.Dual R
      ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).obj X).X n)) :
    singularCochainsEquivTopOpen R X (n + 1)
        (((((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X).d
          (n + 1) n).hom.dualMap φ) =
      (singularCochainCoboundary R X n).app (.op ⊤)
        (singularCochainsEquivTopOpen R X n φ) := by
  ext c
  let C := (singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let e := C.mapIso (Opens.inclusionTopIso X)
  change φ ((C.obj X).d (n + 1) n |>.hom ((e.hom.f (n + 1)).hom c)) =
    φ ((e.hom.f n).hom ((C.obj ((Opens.toTopCat X).obj ⊤)).d (n + 1) n |>.hom c))
  exact congrArg (fun z ↦ φ (ModuleCat.Hom.hom z c)) (e.hom.comm (n + 1) n)

end AlgebraicTopology.Singular
