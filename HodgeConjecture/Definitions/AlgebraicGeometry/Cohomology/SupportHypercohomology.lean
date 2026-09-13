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

public import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeComparison
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportSingularGlobal

import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Hypercohomology and singular cohomology with support

This file develops the bounded-below flasque comparison needed for cohomology with support.
It applies the same explicit injective-replacement argument used for ordinary singular cohomology
to the mapping cone of singular restriction. No hypercohomology spectral sequence is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open Point

universe u v

variable (X : Over (Spec ↧ℂ))

local instance bettiSupportHypercohomologyComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance bettiSupportHypercohomologyAddCommGrpHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard AddCommGrpCat

/-- Conjugating a morphism by two isomorphisms is an additive equivalence of Hom groups. -/
def isoHomCongrAddEquiv
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B') :
    (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr eA eB
  map_add' f g := by simp [Iso.homCongr]

/-- The chosen additive structure on hypercohomology is transported from shifted morphisms in
the derived category. -/
def hypercohomologyAddEquivDerived
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    Hypercohomology X K n ≃+
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n where
  toEquiv := Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q
  map_add' := hypercohomologyEquiv_add X K n

/-- For a K-injective target, shifted derived morphisms are additively identified with
cohomology classes in the Hom complex. -/
def kInjectiveDerivedHomAddEquivCohomologyClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n ≃+
      CochainComplex.HomComplex.CohomologyClass K L n := by
  let qSource : DerivedCategory.Q.obj K ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) :=
    (DerivedCategory.quotientCompQhIso C).symm.app K
  let qTarget : (DerivedCategory.Q.obj L)⟦n⟧ ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧)) :=
    (DerivedCategory.Q.commShiftIso n).symm.app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app (L⟦n⟧)
  let eDerived : ShiftedHom (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) n ≃+
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
    isoHomCongrAddEquiv qSource qTarget
  let qhMap :
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) →+
        (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
          DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
    { toFun := DerivedCategory.Qh.map
      map_zero' := by simp
      map_add' f g := by rw [Functor.map_add] }
  let eQh :
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) ≃+
        (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
          DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))) :=
    AddEquiv.ofBijective qhMap
      (by
        let h := CochainComplex.IsKInjective.Qh_map_bijective
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) (L⟦n⟧)
        exact ⟨fun _ _ hfg ↦ h.injective hfg, h.surjective⟩)
  exact eDerived.trans <| eQh.symm.trans <|
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv.symm

open AlgebraicTopology.Singular

end AlgebraicGeometry.ComplexPoint
