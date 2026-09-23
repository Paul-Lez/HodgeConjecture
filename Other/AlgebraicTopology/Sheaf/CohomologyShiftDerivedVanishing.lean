/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.CohomologySheafSectionDerivedVanishing
public import Other.Algebra.Homology.MapHomologyShift

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {K L : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
lemma mapHomologyShift_eq_zero_of_mapDerivedCategory_eq_zero
    (s n n' : ℤ) (h : s + n = n') (f : K ⟶ L⟦s⟧)
    (hf : F.mapDerivedCategory.map (DerivedCategory.Q.map f) = 0) :
    F.map ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap f n n' h) = 0 := by
  have hz := F.homologyMap_mapHomologicalComplex_eq_zero_of_mapDerivedCategory_eq_zero
    f hf n
  change (HomologicalComplex.homologyFunctor D (.up ℤ) n).map
      ((F.mapHomologicalComplex (.up ℤ)).map f) = 0 at hz
  have hi := CochainComplex.mapHomologyIso_shiftMap F s n n' h f
  dsimp only [Functor.shiftMap, ShiftedHom.map] at hi
  rw [Functor.map_comp, Category.assoc, Category.assoc] at hi
  erw [CochainComplex.mapHomologyIso_shift F L s n n' h] at hi
  rw [← Category.assoc] at hi
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f) F
  change (HomologicalComplex.homologyFunctor D (.up ℤ) n).map
      ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
    (((L⟦s⟧).sc n).mapHomologyIso F).hom =
      ((K.sc n).mapHomologyIso F).hom ≫
        F.map ((HomologicalComplex.homologyFunctor C (.up ℤ) n).map f) at hn
  erw [hn] at hi
  have hbase : ((K.sc n).mapHomologyIso F).hom ≫
      F.map ((HomologicalComplex.homologyFunctor C (.up ℤ) n).map f) = 0 := by
    rw [← hn, hz, zero_comp]
  rw [hbase, zero_comp] at hi
  apply (cancel_epi ((K.sc n).mapHomologyIso F).hom).mp
  simpa only [Functor.shiftMap, Functor.map_comp, Category.assoc, zero_comp, comp_zero] using hi.symm

end CategoryTheory.Functor
