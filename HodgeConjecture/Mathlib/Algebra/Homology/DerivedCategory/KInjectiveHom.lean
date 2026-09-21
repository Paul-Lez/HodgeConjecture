/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

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

end CochainComplex

end
