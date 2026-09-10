/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.MapExtendNaturality

/-! # Naturality of extension across a composite functor

This records the compatibility between extension by zero and a chosen isomorphism
identifying a composite of additive functors.  It is useful when a complex of
global sections is presented as evaluation after forgetting sheaf structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v

variable {C D E : Type u}
  [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  {ι : Type v} {ι' : Type v} {c : ComplexShape ι} {c' : ComplexShape ι'}

set_option backward.isDefEq.respectTransparency false in
/-- The forward map/extension comparison is natural in chain maps. -/
theorem mapExtendIso_hom_naturality
    (F : Functor C D) [F.Additive] {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    (F.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫ extendMap ((F.mapHomologicalComplex c).map f) e := by
  rw [← cancel_epi (mapExtendIso F K e).inv]
  rw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← mapExtendIso_inv_naturality]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero commutes with an isomorphism from a composite of additive functors. -/
theorem mapExtendCompIso_naturality
    (F : Functor C D) [F.Additive] (E₁ : Functor D E) [E₁.Additive]
    (G : Functor C E) [G.Additive] (eComp : F ⋙ E₁ ≅ G)
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    (G.mapHomologicalComplex c').map (extendMap f e) ≫
        (mapExtendIso (c' := c') G L e).hom ≫
        extendMap
          ((Functor.mapHomologicalComplexCompIso eComp c).inv.app L) e =
      (mapExtendIso (c' := c') G K e).hom ≫
        extendMap
          ((Functor.mapHomologicalComplexCompIso eComp c).inv.app K) e ≫
        extendMap
          ((E₁.mapHomologicalComplex c).map
            ((F.mapHomologicalComplex c).map f)) e := by
  rw [← Category.assoc, mapExtendIso_hom_naturality]
  simp only [Category.assoc]
  rw [← extendMap_comp, ← extendMap_comp]
  rw [(Functor.mapHomologicalComplexCompIso eComp c).inv.naturality]
  rfl

end HomologicalComplex
