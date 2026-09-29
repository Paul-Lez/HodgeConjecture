/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality

/-! # Naturality of positive canonical cone boundaries -/

open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace CochainComplex.mappingCocone
variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex (CochainComplex C ℤ)}

/-- Positive canonical cone boundaries are natural for maps of short exact sequences. -/
lemma shortExactHomologyIsoCone_inv_inr_naturality (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n n' : ℤ) (h : 1 + n = n') :
    HomologicalComplex.homologyMap (mappingCone.inr S.g) n ≫
      (shortExactHomologyIsoCone S hS n n' h).inv ≫
        HomologicalComplex.homologyMap f.τ₁ n' =
    HomologicalComplex.homologyMap f.τ₃ n ≫
      HomologicalComplex.homologyMap (mappingCone.inr T.g) n ≫
        (shortExactHomologyIsoCone T hT n n' h).inv := by
  let eS := shortExactHomologyIsoCone S hS n n' h
  let eT := shortExactHomologyIsoCone T hT n n' h
  let k := mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm
  have hn : HomologicalComplex.homologyMap f.τ₁ n' ≫ eT.hom =
      eS.hom ≫ HomologicalComplex.homologyMap k n :=
    shortExactHomologyIsoCone_naturality f hS hT n n' h
  have he : eS.inv ≫ HomologicalComplex.homologyMap f.τ₁ n' =
      HomologicalComplex.homologyMap k n ≫ eT.inv := by
    apply (cancel_mono eT.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hi : mappingCone.inr S.g ≫ k = f.τ₃ ≫ mappingCone.inr T.g := by
    simp [k, mappingCone.map]
  change _ ≫ (eS.inv ≫ _) = _ ≫ _ ≫ eT.inv
  rw [he, ← Category.assoc, ← HomologicalComplex.homologyMap_comp, hi,
    HomologicalComplex.homologyMap_comp, Category.assoc]
end CochainComplex.mappingCocone
