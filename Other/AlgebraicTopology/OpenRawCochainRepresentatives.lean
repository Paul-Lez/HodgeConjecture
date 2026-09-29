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
  erw [HomologicalComplex.mapExtendCanonicalIso_hom_f (forget₂ (ModuleCat R) AddCommGrpCat)
    (SingularChainComplex R (TopCat.of V)).linearDualCochainComplex
    ComplexShape.embeddingUpNat (i := n) (j := (n : ℤ)) rfl]
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
