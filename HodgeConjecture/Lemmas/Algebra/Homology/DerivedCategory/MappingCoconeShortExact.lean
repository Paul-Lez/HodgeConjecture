/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.Algebra.Homology.DerivedCategory.MappingCoconeShortExact

/-!
# The canonical homotopy fiber comparison for a short exact sequence

Lemmas about the definitions in
`HodgeConjecture.Definitions.Algebra.Homology.DerivedCategory.MappingCoconeShortExact`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCone

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A map of mapping cones induced by quasi-isomorphisms is a quasi-isomorphism. -/
lemma quasiIso_map_of_quasiIso {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : f₁ ≫ b = a ≫ f₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (map f₁ f₂ a b h) := by
  let := HasDerivedCategory.standard C
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).1
  exact isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map (triangleMap f₁ f₂ a b h))
    (DerivedCategory.mappingCone_triangle_distinguished f₁)
    (DerivedCategory.mappingCone_triangle_distinguished f₂)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map a)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map b)))

end mappingCone

namespace mappingCocone

variable (S : ShortComplex (CochainComplex C ℤ))

lemma quasiIso_shiftedLiftShortComplex (hS : S.ShortExact) :
    QuasiIso (shiftedLiftShortComplex S) := by
  have := mappingCone.quasiIso_descShortComplex hS
  have := mappingCone.quasiIso_map_of_quasiIso
    (mappingCone.inr S.f) S.g (𝟙 _) (mappingCone.descShortComplex S) (by simp)
  dsimp only [shiftedLiftShortComplex]
  infer_instance

end mappingCocone

end CochainComplex
