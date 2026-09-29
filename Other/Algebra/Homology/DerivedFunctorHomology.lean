/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

open CategoryTheory CategoryTheory.Limits HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)
  (g : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
    (F.mapHomologicalComplex (.up ℤ)).obj L)

omit [HasDerivedCategory C] in
lemma map_homologyMap_eq_of_Q_map_eq
    (hfg : DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) =
      DerivedCategory.Q.map g) (n : ℤ) :
    F.map (HomologicalComplex.homologyMap f n) =
      ((K.sc n).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap g n ≫
        ((L.sc n).mapHomologyIso F).hom := by
  have hh : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map f) n =
      HomologicalComplex.homologyMap g n := by
    apply (cancel_epi ((DerivedCategory.homologyFunctorFactors D n).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K))).mp
    rw [← DerivedCategory.homologyFunctorFactors_hom_naturality,
      ← DerivedCategory.homologyFunctorFactors_hom_naturality, hfg]
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor _ (.up ℤ) n).map f) F
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map f) n ≫
      ((L.sc n).mapHomologyIso F).hom =
    ((K.sc n).mapHomologyIso F).hom ≫ F.map
      (HomologicalComplex.homologyMap f n) at hn
  rw [hh] at hn
  apply (cancel_epi ((K.sc n).mapHomologyIso F).hom).mp
  simpa only [Iso.hom_inv_id_assoc] using hn.symm

lemma map_homologyMap_eq_of_derived_square
    (hfg : F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        F.mapDerivedCategoryFactors.hom.app L =
      F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map g)
    (n : ℤ) :
    F.map (HomologicalComplex.homologyMap f n) =
      ((K.sc n).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap g n ≫
        ((L.sc n).mapHomologyIso F).hom := by
  apply F.map_homologyMap_eq_of_Q_map_eq f g _ n
  apply (cancel_epi (F.mapDerivedCategoryFactors.hom.app K)).mp
  rw [← F.mapDerivedCategoryFactors_hom_naturality f]
  exact hfg

end CategoryTheory.Functor
