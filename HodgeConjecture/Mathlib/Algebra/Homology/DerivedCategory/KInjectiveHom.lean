/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import HodgeConjecture.Mathlib.Algebra.Homology.HomComplexPrecomp

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Morphisms in the derived category into a K-injective complex

For a K-injective complex `L`, morphisms `K → L[n]` in the derived category are chain maps modulo
homotopy, that is cohomology classes of the Hom complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace CategoryTheory

/-- In a preadditive category, let `eA : A ≅ A'` and `eB : B ≅ B'` be isomorphisms. This additive
equivalence sends `f : A → B` to `eB ∘ f ∘ eA⁻¹ : A' → B'`. -/
def isoHomCongrAddEquiv
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B') :
    (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr eA eB
  map_add' f g := by simp [Iso.homCongr]

@[simp]
lemma isoHomCongrAddEquiv_apply
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) :
    isoHomCongrAddEquiv eA eB f = eA.inv ≫ f ≫ eB.hom := rfl

end CategoryTheory

namespace CochainComplex

/-- Let `K` and `L` be integer-indexed cochain complexes in an abelian category, with `L`
K-injective, and let `n` be an integer. This additive equivalence identifies `Hom_D(K, L[n])`
with degree-`n` cocycles in the Hom complex modulo coboundaries, or equivalently chain maps `K →
L[n]` modulo chain homotopy. -/
def kInjectiveDerivedHomAddEquivCohomologyClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n ≃+
      CochainComplex.HomComplex.CohomologyClass K L n :=
  let qSource : DerivedCategory.Q.obj K ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C ℤᵘᵖ).obj K) :=
    (DerivedCategory.quotientCompQhIso C).symm.app K
  let qTarget : (DerivedCategory.Q.obj L)⟦n⟧ ≅
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C ℤᵘᵖ).obj (L⟦n⟧)) :=
    (DerivedCategory.Q.commShiftIso n).symm.app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app (L⟦n⟧)
  let eDerived : ShiftedHom (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) n ≃+
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C ℤᵘᵖ).obj K) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C ℤᵘᵖ).obj (L⟦n⟧))) :=
    isoHomCongrAddEquiv qSource qTarget
  let qhMap :
      (((HomotopyCategory.quotient C ℤᵘᵖ).obj K ⟶
          (HomotopyCategory.quotient C ℤᵘᵖ).obj (L⟦n⟧))) →+
        (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C ℤᵘᵖ).obj K) ⟶
          DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C ℤᵘᵖ).obj (L⟦n⟧))) :=
    { toFun := DerivedCategory.Qh.map
      map_zero' := by simp
      map_add' f g := by rw [Functor.map_add] }
  let eQh :
      (((HomotopyCategory.quotient C ℤᵘᵖ).obj K ⟶
          (HomotopyCategory.quotient C ℤᵘᵖ).obj (L⟦n⟧))) ≃+
        (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C ℤᵘᵖ).obj K) ⟶
          DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient C ℤᵘᵖ).obj (L⟦n⟧))) :=
    AddEquiv.ofBijective qhMap
      (by
        let h := CochainComplex.IsKInjective.Qh_map_bijective
          ((HomotopyCategory.quotient C ℤᵘᵖ).obj K) (L⟦n⟧)
        exact ⟨fun _ _ hfg ↦ h.injective hfg, h.surjective⟩)
  eDerived.trans <| eQh.symm.trans <|
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv.symm

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle K L n) :
    (kInjectiveDerivedHomAddEquivCohomologyClass K L n).symm
      (CochainComplex.HomComplex.CohomologyClass.mk z) =
    ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
      DerivedCategory.Q := by
  dsimp [kInjectiveDerivedHomAddEquivCohomologyClass, isoHomCongrAddEquiv, ShiftedHom.map]
  rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk]
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality
    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identification is natural in the source complex. -/
lemma kInjectiveDerivedHomAddEquivCohomologyClass_precomp
    {A A' : CochainComplex C ℤ} (g : A' ⟶ A) (L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ)
    (x : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj L) n) :
    kInjectiveDerivedHomAddEquivCohomologyClass A' L n (DerivedCategory.Q.map g ≫ x) =
      CochainComplex.HomComplex.precompClass g L n
        (kInjectiveDerivedHomAddEquivCohomologyClass A L n x) := by
  apply (kInjectiveDerivedHomAddEquivCohomologyClass A' L n).symm.injective
  rw [AddEquiv.symm_apply_apply]
  obtain ⟨x, rfl⟩ := (kInjectiveDerivedHomAddEquivCohomologyClass A L n).symm.surjective x
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [AddEquiv.apply_symm_apply, CochainComplex.HomComplex.precompClass_mk,
    kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
    kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]

end CochainComplex

end
