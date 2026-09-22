/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality

/-!
# MappingCoconeShortExactNaturality

Lemmas about the definitions in
`HodgeConjecture.Definitions.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCocone

variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex (CochainComplex C ℤ)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit shifted fiber lift is natural for actual short-complex
maps, before passing to any derived or homotopy category. -/
@[reassoc]
lemma shiftedLiftShortComplex_naturality (f : S ⟶ T) :
    f.τ₁⟦(1 : ℤ)⟧' ≫ shiftedLiftShortComplex T =
      shiftedLiftShortComplex S ≫
        mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm := by
  ext n
  simp [shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun g => g.f (n + 1) ≫ (mappingCone.inl T.g).v (n + 1) n (by omega))
      f.comm₁₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality on homology of the canonical cone comparison. -/
@[reassoc]
lemma shortExactHomologyIsoCone_naturality (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n n' : ℤ) (h : 1 + n = n') :
    HomologicalComplex.homologyMap f.τ₁ n' ≫
      (shortExactHomologyIsoCone T hT n n' h).hom =
    (shortExactHomologyIsoCone S hS n n' h).hom ≫
      HomologicalComplex.homologyMap
        (mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm) n := by
  let H := HomologicalComplex.homologyFunctor C ℤᵘᵖ 0
  change (H.shift n').map f.τ₁ ≫
      (((H.shiftIso 1 n n' h).inv.app T.X₁) ≫
        (H.shift n).map (shiftedLiftShortComplex T)) =
    ((H.shiftIso 1 n n' h).inv.app S.X₁ ≫
      (H.shift n).map (shiftedLiftShortComplex S)) ≫
      (H.shift n).map (mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm)
  rw [(H.shiftIso 1 n n' h).inv.naturality_assoc f.τ₁,
    Functor.comp_map, ← Functor.map_comp, shiftedLiftShortComplex_naturality, Functor.map_comp,
    Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-one morphism in the cone triangle for the injection in a short
exact sequence induces the ordinary connecting morphism after the canonical
comparison from the cone to the quotient. -/
lemma shiftMap_mappingCone_triangle_mor₃_eq_desc_δ
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (n n' : ℤ) (h : 1 + n = n') :
    (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
        (mappingCone.triangle S.f).mor₃ n n' h =
      HomologicalComplex.homologyMap (mappingCone.descShortComplex S) n ≫
        hS.δ n n' (by simpa [add_comm] using h) := by
  have ht := mappingCone.homologySequenceδ_triangleh hS n n'
    (by simpa [add_comm] using h)
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at ht
  have ht₁ := (cancel_epi
    ((HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).hom.app _)).mp ht
  rw [← Category.assoc] at ht₁
  exact (cancel_mono
    ((HomotopyCategory.homologyFunctorFactors C (.up ℤ) n').inv.app
      (mappingCone.triangle S.f).obj₁)).mp ht₁

/-- Rewriting the shifted homology map of a cone triangle as an ordinary
homology map followed by the homology shift comparison. -/
lemma shiftMap_mappingCone_triangle_mor₃ (S : ShortComplex (CochainComplex C ℤ))
    (n : ℤ) (h : 1 + n = n + 1) :
    (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
        (mappingCone.triangle S.f).mor₃ n (n + 1) h =
      HomologicalComplex.homologyMap (mappingCone.triangle S.f).mor₃ n ≫
        ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          1 n (n + 1) h).hom.app S.X₁ := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The second morphism of the quotient cone triangle, transported through
the canonical short-exact-sequence cone comparison, is the connecting
morphism. In particular, this fixes the comparison with positive sign. -/
theorem homologyMap_mappingCone_triangle_mor₂_shortExactHomologyIsoCone_inv
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (n n' : ℤ) (h : 1 + n = n') :
    HomologicalComplex.homologyMap (mappingCone.triangle S.g).mor₂ n ≫
      (shortExactHomologyIsoCone S hS n n' h).inv =
    hS.δ n n' (by simpa [add_comm] using h) := by
  have hn : n' = n + 1 := by omega
  cases hn
  let p : 1 + n = n + 1 := by omega
  have hp : h = p := Subsingleton.elim _ _
  cases hp
  let : QuasiIso (mappingCone.descShortComplex S) :=
    mappingCone.quasiIso_descShortComplex hS
  let eD := asIso
    (HomologicalComplex.homologyMap (mappingCone.descShortComplex S) n)
  let E := shortExactHomologyIsoCone S hS n (n + 1) p
  let : QuasiIso (shiftedLiftShortComplex S) := quasiIso_shiftedLiftShortComplex S hS
  let : IsIso (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n) :=
    (quasiIsoAt_iff_isIso_homologyMap (shiftedLiftShortComplex S) n).mp inferInstance
  apply (cancel_mono E.hom).1
  simp only [Category.assoc, E, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi eD.hom).1
  let M := mappingCone.map (mappingCone.inr S.f) S.g
    (𝟙 _) (mappingCone.descShortComplex S) (by simp)
  have hrot := (mappingCone.rotateHomotopyEquivComm₂Homotopy S.f).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_comp] at hrot
  have hcone := (mappingCone.triangleMap
    (mappingCone.inr S.f) S.g
    (𝟙 _) (mappingCone.descShortComplex S) (by simp)).comm₂
  have hcone' := congrArg (fun q => HomologicalComplex.homologyMap q n) hcone
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hcone'
  change HomologicalComplex.homologyMap
      (mappingCone.inr (mappingCone.inr S.f)) n ≫
      HomologicalComplex.homologyMap M n =
    HomologicalComplex.homologyMap (mappingCone.descShortComplex S) n ≫
      HomologicalComplex.homologyMap (mappingCone.triangle S.g).mor₂ n at hcone'
  change HomologicalComplex.homologyMap (mappingCone.descShortComplex S) n ≫
      HomologicalComplex.homologyMap (mappingCone.triangle S.g).mor₂ n =
    HomologicalComplex.homologyMap (mappingCone.descShortComplex S) n ≫
      hS.δ n (n + 1) (by simp) ≫ E.hom
  erw [← hcone']
  change HomologicalComplex.homologyMap
      (mappingCone.inr (mappingCone.inr S.f)) n ≫
      HomologicalComplex.homologyMap M n = _
  rw [← hrot, Category.assoc]
  conv_rhs =>
    rw [← Category.assoc,
      ← shiftMap_mappingCone_triangle_mor₃_eq_desc_δ S hS n (n + 1) (by omega)]
  rw [shiftMap_mappingCone_triangle_mor₃ S]
  dsimp only [E, shortExactHomologyIsoCone, Iso.trans_hom]
  have hcancel :
      ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          1 n (n + 1) p).hom.app S.X₁ ≫
        (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          1 n (n + 1) p).app S.X₁).symm.hom = 𝟙 _ :=
    ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
      1 n (n + 1) p).hom_inv_id_app S.X₁
  have hcancel_assoc :
      ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
          1 n (n + 1) p).hom.app S.X₁ ≫
        ((((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
            1 n (n + 1) p).app S.X₁).symm.hom ≫
          (asIso (HomologicalComplex.homologyMap
            (shiftedLiftShortComplex S) n)).hom) =
      (asIso (HomologicalComplex.homologyMap
        (shiftedLiftShortComplex S) n)).hom := by
    rw [← Category.assoc, hcancel, Category.id_comp]
  rw [Category.assoc, hcancel_assoc]
  dsimp only [shiftedLiftShortComplex]
  simp only [HomologicalComplex.homologyMap_comp]
  rfl

end CochainComplex.mappingCocone
