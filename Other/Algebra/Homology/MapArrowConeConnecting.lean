/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality

/-! # The actual arrow-isomorphism cone map preserves its connecting morphism -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [Abelian C]
  {K L K' L' : CochainComplex C ℤ} (f : K ⟶ L) (g : K' ⟶ L')

/-- Mathlib's general homotopy-cofiber arrow map is the actual standard cone map
for integer cochain complexes. -/
theorem homotopyCofiber_mapArrowHom_eq (a : Arrow.mk f ⟶ Arrow.mk g) :
    HomologicalComplex.homotopyCofiber.mapArrowHom f g
      (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩) a =
      map f g a.left a.right a.w.symm := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map,
    HomologicalComplex.homotopyCofiber.mapArrowHom,
    inl, inr, desc, descCochain, fst, snd,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  rw [HomComplex.Cochain.comp_v _ _ _ n (n + 1) n rfl (by omega)]
  simp

/-- The actual cone isomorphism induced by an arrow isomorphism preserves the
prescribed negative connecting projection, not merely the cone's isomorphism class. -/
@[reassoc]
theorem homotopyCofiber_mapArrowIso_connecting (e : Arrow.mk f ≅ Arrow.mk g) :
    (HomologicalComplex.homotopyCofiber.mapArrowIso f g
      (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩) e).hom ≫
      (triangle g).mor₃ = (triangle f).mor₃ ≫ e.hom.left⟦(1 : ℤ)⟧' := by
  change HomologicalComplex.homotopyCofiber.mapArrowHom f g _ e.hom ≫ _ = _
  rw [homotopyCofiber_mapArrowHom_eq]
  exact (triangleMap f g e.hom.left e.hom.right e.hom.w.symm).comm₃.symm

end CochainComplex.mappingCone
