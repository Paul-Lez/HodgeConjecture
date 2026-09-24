/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Connecting maps under extension of the grading

Extension by zero along an embedding of complex shapes preserves the connecting map
of a short exact sequence, under the actual extension homology isomorphisms. The
comparison is induced by a morphism of the snake-lemma diagrams.
-/

open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace HomologicalComplex
variable {C ι ι' : Type*} [Category* C] [Abelian C]
  {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {K L : HomologicalComplex C c}

/-- Extension's opcycle identification is natural in the complex. -/
lemma extendOpcyclesIso_hom_naturality (f : K ⟶ L) {i : ι} {i' : ι'}
    (hi : e.f i = i') :
    opcyclesMap (extendMap f e) i' ≫ (L.extendOpcyclesIso e hi).hom =
      (K.extendOpcyclesIso e hi).hom ≫ opcyclesMap f i := by
  simp [← cancel_epi ((K.extend e).pOpcycles i'), extendMap_f f e hi]

/-- Extension preserves the map from opcycles to cycles induced by the differential. -/
lemma extendOpcyclesIso_hom_opcyclesToCycles (K : HomologicalComplex C c)
    {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extendOpcyclesIso e hi).hom ≫ K.opcyclesToCycles i j =
      (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj).hom := by
  rw [← cancel_epi ((K.extend e).pOpcycles i'), ← cancel_mono (K.iCycles j)]
  simp only [Category.assoc, pOpcycles_extendOpcyclesIso_hom_assoc,
    pOpcycles_opcyclesToCycles_iCycles, extendCyclesIso_hom_iCycles,
    pOpcycles_opcyclesToCycles_iCycles_assoc, extend_d_eq K e hi hj,
    Iso.inv_hom_id, Category.comp_id]

variable (S : ShortComplex (HomologicalComplex C c))

/-- The homology row of the extension comparison of snake diagrams. -/
def extendHomologyShortComplexMap {i : ι} {i' : ι'} (hi : e.f i = i') :
    (S.map (e.extendFunctor C)).map (homologyFunctor C c' i') ⟶
      S.map (homologyFunctor C c i) where
  τ₁ := (S.X₁.extendHomologyIso e hi).hom
  τ₂ := (S.X₂.extendHomologyIso e hi).hom
  τ₃ := (S.X₃.extendHomologyIso e hi).hom
  comm₁₂ := (extendHomologyIso_hom_naturality S.f e hi).symm
  comm₂₃ := (extendHomologyIso_hom_naturality S.g e hi).symm

/-- The cycle row of the extension comparison of snake diagrams. -/
def extendCyclesShortComplexMap {i : ι} {i' : ι'} (hi : e.f i = i') :
    (S.map (e.extendFunctor C)).map (cyclesFunctor C c' i') ⟶
      S.map (cyclesFunctor C c i) where
  τ₁ := (S.X₁.extendCyclesIso e hi).hom
  τ₂ := (S.X₂.extendCyclesIso e hi).hom
  τ₃ := (S.X₃.extendCyclesIso e hi).hom
  comm₁₂ := (extendCyclesIso_hom_naturality S.f e hi).symm
  comm₂₃ := (extendCyclesIso_hom_naturality S.g e hi).symm

/-- The opcycle row of the extension comparison of snake diagrams. -/
def extendOpcyclesShortComplexMap {i : ι} {i' : ι'} (hi : e.f i = i') :
    (S.map (e.extendFunctor C)).map (opcyclesFunctor C c' i') ⟶
      S.map (opcyclesFunctor C c i) where
  τ₁ := (S.X₁.extendOpcyclesIso e hi).hom
  τ₂ := (S.X₂.extendOpcyclesIso e hi).hom
  τ₃ := (S.X₃.extendOpcyclesIso e hi).hom
  comm₁₂ := (extendOpcyclesIso_hom_naturality e S.f hi).symm
  comm₂₃ := (extendOpcyclesIso_hom_naturality e S.g hi).symm

/-- Extension's homology, cycle and opcycle identifications form a snake-diagram map. -/
def extendSnakeInputMap (hS : S.ShortExact)
    (hE : (S.map (e.extendFunctor C)).ShortExact)
    {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j')
    (hij : c.Rel i j) (hij' : c'.Rel i' j') :
    HomologySequence.snakeInput hE i' j' hij' ⟶
      HomologySequence.snakeInput hS i j hij where
  f₀ := extendHomologyShortComplexMap e S hi
  f₁ := extendOpcyclesShortComplexMap e S hi
  f₂ := extendCyclesShortComplexMap e S hj
  f₃ := extendHomologyShortComplexMap e S hj
  comm₀₁ := by
    ext <;> apply extendHomologyIso_hom_homologyι
  comm₁₂ := by
    ext <;> apply extendOpcyclesIso_hom_opcyclesToCycles
  comm₂₃ := by
    ext <;> exact (homologyπ_extendHomologyIso_hom _ _ _).symm

/-- The actual extension homology isomorphisms preserve connecting morphisms. -/
lemma extend_connecting (hS : S.ShortExact)
    (hE : (S.map (e.extendFunctor C)).ShortExact)
    {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j')
    (hij : c.Rel i j) (hij' : c'.Rel i' j') :
    hE.δ i' j' hij' ≫ (S.X₁.extendHomologyIso e hj).hom =
      (S.X₃.extendHomologyIso e hi).hom ≫ hS.δ i j hij :=
  ShortComplex.SnakeInput.naturality_δ (extendSnakeInputMap e S hS hE hi hj hij hij')

end HomologicalComplex
