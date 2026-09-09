/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Other.Algebra.Homology.HomComplexShiftNaturality

/-! # Exact functors preserve the canonical homology shift -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

omit [F.PreservesHomology] in
/-- Applying an exact additive functor commutes with the middle component of
the canonical three-term homology shift. This fixes the shift sign without
choosing a homology equivalence. -/
theorem map_shiftShortComplex_middle (K : CochainComplex C ℤ)
    (t n n' : ℤ) (h : t + n = n') :
    (((HomologicalComplex.shortComplexFunctor D (.up ℤ) n).map
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso t).hom.app K)) ≫
        (shiftShortComplexFunctorIso D t n n' h).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K)).τ₂ =
      (F.mapShortComplex.map ((shiftShortComplexFunctorIso C t n n' h).hom.app K)).τ₂ := by
  subst n'
  simp [shiftShortComplexFunctorIso, shiftShortComplexFunctor', shiftEval,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

/-- The canonical homology comparison for an exact additive functor preserves
the prescribed homology shift, including the signs of adjacent differentials. -/
theorem mapHomologyIso_shift (K : CochainComplex C ℤ)
    (t n n' : ℤ) (h : t + n = n') :
    HomologicalComplex.homologyMap
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso t).hom.app K) n ≫
      ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso t n n' h).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      ((K.sc n').mapHomologyIso F).hom =
    (((K⟦t⟧).sc n).mapHomologyIso F).hom ≫
      F.map (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso t n n' h).hom.app K) := by
  have hh := ShortComplex.homologyMap_eq_of_middle_eq _ _
    (map_shiftShortComplex_middle F K t n n' h)
  rw [ShortComplex.homologyMap_comp] at hh
  change HomologicalComplex.homologyMap
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso t).hom.app K) n ≫
    ShortComplex.homologyMap ((shiftShortComplexFunctorIso D t n n' h).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)) = _ at hh
  rw [← ShiftSequence.shiftIso_hom_app] at hh
  rw [← Category.assoc]
  erw [hh]
  rw [ShortComplex.mapHomologyIso_hom_naturality]
  exact congrArg (fun f => (((K⟦t⟧).sc n).mapHomologyIso F).hom ≫ F.map f)
    (ShiftSequence.shiftIso_hom_app t n n' h K).symm

/-- Exact additive functors commute with the shifted homology map of an actual
shifted chain morphism. In particular this applies to cone connecting maps. -/
theorem mapHomologyIso_shiftMap {K L : CochainComplex C ℤ}
    (t n n' : ℤ) (h : t + n = n') (f : K ⟶ L⟦t⟧) :
    (HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftMap
        (ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ))) n n' h ≫
      ((L.sc n').mapHomologyIso F).hom =
    ((K.sc n).mapHomologyIso F).hom ≫
      F.map ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap f n n' h) := by
  dsimp only [Functor.shiftMap, ShiftedHom.map]
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  erw [mapHomologyIso_shift]
  rw [← Category.assoc]
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map f) F
  change (HomologicalComplex.homologyFunctor D (.up ℤ) n).map
      ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
    (((L⟦t⟧).sc n).mapHomologyIso F).hom =
      ((K.sc n).mapHomologyIso F).hom ≫
        F.map ((HomologicalComplex.homologyFunctor C (.up ℤ) n).map f) at hn
  erw [hn]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end CochainComplex
