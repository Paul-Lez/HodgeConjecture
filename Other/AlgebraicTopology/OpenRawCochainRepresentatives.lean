/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenRawBoundaryComparison

/-!
# Raw cochain representatives under the prescribed identifications

The raw/dual integer cochain comparison is the identity on representatives after
its grading isomorphisms. The coefficient-forgetting homology comparison also
preserves the class of an actual cycle, through its canonical cycle comparison.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u v

namespace HomologicalComplex
variable {C D : Type u} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex C c)
  (e : c.Embedding c') [e.IsRelIff]
omit [e.IsRelIff] in
lemma mapExtendIso_hom_f {p : i} {q : i'} (h : e.f p = q) :
    (mapExtendIso F K e).hom.f q =
    F.map (K.extendXIso e h).hom ≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  change (mapExtendXIsoAux F K (e.r q)).hom =
    F.map (extend.XIso K (e.r_eq_some h)).hom ≫
      (extend.XIso ((F.mapHomologicalComplex c).obj K) (e.r_eq_some h)).inv
  have H (a : Option i) (ha : a = some p) :
      (mapExtendXIsoAux F K a).hom = F.map (extend.XIso K ha).hom ≫
        (extend.XIso ((F.mapHomologicalComplex c).obj K) ha).inv := by
    subst a
    simp [mapExtendXIsoAux, extend.XIso]
    rfl
  exact H _ _
end HomologicalComplex
namespace AlgebraicTopology.Singular
variable (R : Type) [Field R] (X : TopCat.{0}) (V : Opens X)
lemma openRawSingularCochainComplexIntIsoDual_inv_f (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map
      (((SingularChainComplex R (TopCat.of V)).linearDualCochainComplex.extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).inv) ≫
      (openRawSingularCochainComplexIntIsoDual R X V).inv.f (n : ℤ) =
    (openRawSingularCochainComplexIsoDual R X V).inv.f n ≫
      ((openRawSingularCochainComplex R X V).extendXIso
        ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).inv := by
  dsimp only [openRawSingularCochainComplexIntIsoDual, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv]
  rw [HomologicalComplex.comp_f]
  erw [HomologicalComplex.mapExtendIso_hom_f (forget₂ (ModuleCat R) AddCommGrpCat)
    (SingularChainComplex R (TopCat.of V)).linearDualCochainComplex
    ComplexShape.embeddingUpNat (p := n) (q := (n : ℤ)) rfl]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := n) rfl]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
end AlgebraicTopology.Singular

namespace CategoryTheory.ShortComplex
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (S : ShortComplex C) (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
lemma homologyπ_mapHomologyIso_hom :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    Category.assoc]
  change (h.map F).cyclesIso.hom ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
  rw [← Functor.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv, Functor.map_comp, Category.assoc]
end CategoryTheory.ShortComplex
