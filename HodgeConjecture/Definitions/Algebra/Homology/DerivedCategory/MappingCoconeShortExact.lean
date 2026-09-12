/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The canonical homotopy fiber comparison for a short exact sequence

For `0 → A → B → C → 0` this file constructs the canonical quasi-isomorphism
`A → mappingCocone (B → C)`. Its normalization is the actual inclusion `A → B`.
The proof uses the explicit mapping-cone rotation homotopy equivalence and the
canonical quasi-isomorphism from the cone of `A → B` to `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

attribute [local implicit_reducible] CategoryTheory.Functor.mapTriangle
  CochainComplex.mappingCone CochainComplex.mappingCone.triangle
  CategoryTheory.Pretriangulated.Triangle.mk shiftFunctorCompIsoId
  CochainComplex.shiftFunctor CochainComplex.mappingCocone CochainComplex.HomComplex.Cocycle.mk

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCone

/-- A map of mapping cones induced by quasi-isomorphisms is a quasi-isomorphism. -/
lemma quasiIso_map_of_quasiIso {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : f₁ ≫ b = a ≫ f₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (map f₁ f₂ a b h) := by
  let := HasDerivedCategory.standard C
  refine (DerivedCategory.isIso_Q_map_iff_quasiIso C _).1 ?_
  rw [← triangleMap_hom₃, ← DerivedCategory.Q.mapTriangle_map_hom₃]
  with_implicit
  exact isIso₃_of_isIso₁₂ (DerivedCategory.Q.mapTriangle.map (triangleMap f₁ f₂ a b h))
    (DerivedCategory.mappingCone_triangle_distinguished f₁)
    (DerivedCategory.mappingCone_triangle_distinguished f₂)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map a)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map b)))

end mappingCone

namespace mappingCocone

variable (S : ShortComplex (CochainComplex C ℤ))

/-- The explicit rotated-cone comparison, before shifting back to the homotopy
fiber. It is built from canonical chain maps, not from a choice of a completion
of a morphism of distinguished triangles. -/
def shiftedLiftShortComplex : S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (mappingCone.rotateHomotopyEquiv S.f).hom ≫
    mappingCone.map (mappingCone.inr S.f) S.g (𝟙 _)
      (mappingCone.descShortComplex S) (by simp)

/-- Canonical comparison from the first term of a short complex to the homotopy
fiber of its second map. -/
abbrev liftShortComplex : S.X₁ ⟶ mappingCocone S.g :=
  (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).inv.app S.X₁ ≫
    (shiftedLiftShortComplex S)⟦(-1 : ℤ)⟧'

attribute [local instance] mappingCone.quasiIso_map_of_quasiIso in
lemma quasiIso_shiftedLiftShortComplex (hS : S.ShortExact) :
    QuasiIso (shiftedLiftShortComplex S) := by
  have := mappingCone.quasiIso_descShortComplex hS
  rw [shiftedLiftShortComplex]
  infer_instance

lemma quasiIso_liftShortComplex (hS : S.ShortExact) :
    QuasiIso (liftShortComplex S) := by
  have := quasiIso_shiftedLiftShortComplex S hS
  infer_instance

/-- The rotated-cone lift, followed by the connecting map of the mapping-cone triangle of
`S.g`, is `-S.f⟦1⟧'`. -/
lemma shiftedLiftShortComplex_comp_triangle_mor₃ :
    shiftedLiftShortComplex S ≫ (mappingCone.triangle S.g).mor₃ = -(S.f⟦(1 : ℤ)⟧') := by
  rw [shiftedLiftShortComplex, Category.assoc, mappingCone.map_eq_mapOfHomotopy,
    mappingCone.triangleMapOfHomotopy_comm₃, ← Category.assoc,
    mappingCone.rotateHomotopyEquiv_comm₃, Preadditive.neg_comp, ← Functor.map_comp,
    Category.comp_id]

/-- The first projection of a mapping cocone is, up to sign, the `(-1)`-shift of the connecting
map of the mapping-cone triangle, transported back along `K⟦1⟧⟦-1⟧ ≅ K`. -/
lemma fst_eq_neg_shift_triangle_mor₃ {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    fst φ = -((mappingCone.triangle φ).mor₃⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (CochainComplex C ℤ) 1 (-1) (by lia)).hom.app K) := by
  ext n
  simp [fst, mappingCone.triangle, HomComplex.Cochain.leftShift_v (n := 1) _ (-1) 0 _ n n _ (n + -1),
    HomComplex.Cochain.rightShift_v (n := 1) _ 1 0 _ (n + -1) (n + -1) _ n,
    shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f, shiftFunctor]

@[reassoc (attr := simp)]
lemma liftShortComplex_fst : liftShortComplex S ≫ fst S.g = S.f := by
  simp [fst_eq_neg_shift_triangle_mor₃, liftShortComplex,
    ← Functor.map_comp_assoc, shiftedLiftShortComplex_comp_triangle_mor₃, ← Functor.comp_map]

@[reassoc (attr := simp)]
lemma liftShortComplex_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (liftShortComplex S).f p ≫ (snd S.g).v p q hpq = 0 := by
  subst q
  simp [liftShortComplex, shiftedLiftShortComplex, snd,
    shiftFunctorCompIsoId, shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    mappingCone.rotateHomotopyEquiv, mappingCone.map,
    mappingCone.lift_f _ _ _ _ (p + -1) p (by omega),
    HomComplex.Cochain.leftShift, shiftFunctor]

/-- The rotated-cone formula is exactly the standard fiber lift with the zero
nullhomotopy of `S.f ≫ S.g = 0`. Thus its chain-level normalization is canonical. -/
lemma liftShortComplex_eq_lift :
    liftShortComplex S = lift S.g S.f 0 (by simp) := by
  ext p
  calc
    _ = (liftShortComplex S).f p ≫ 𝟙 _ := by simp
    _ = (liftShortComplex S).f p ≫
        ((fst S.g).f p ≫ (inl S.g).v p p (add_zero p) +
          (snd S.g).v p (p + -1) rfl ≫ (inr S.g).1.v (p + -1) p (by omega)) := by
      rw [id_X]
    _ = (lift S.g S.f 0 (by simp)).f p ≫
        ((fst S.g).f p ≫ (inl S.g).v p p (add_zero p) +
          (snd S.g).v p (p + -1) rfl ≫ (inr S.g).1.v (p + -1) p (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, liftShortComplex_f_snd_v,
        zero_comp, add_zero, lift_f_fst_f, lift_f_snd_v,
        HomComplex.Cochain.zero_v]
      exact congrArg (fun f : S.X₁ ⟶ S.X₂ => f.f p ≫ (inl S.g).v p p (add_zero p))
        (liftShortComplex_fst S)
    _ = _ := by rw [id_X]; simp

end mappingCocone

end CochainComplex
