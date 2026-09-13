/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExact

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCocone

variable (S : ShortComplex (CochainComplex C ℤ))

/-- Canonical comparison from the first term of a short complex to the homotopy
fiber of its second map. -/
def liftShortComplex : S.X₁ ⟶ mappingCocone S.g :=
  (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).inv.app S.X₁ ≫
    (shiftedLiftShortComplex S)⟦(-1 : ℤ)⟧'
set_option backward.isDefEq.respectTransparency false in
lemma quasiIso_liftShortComplex (hS : S.ShortExact) :
    QuasiIso (liftShortComplex S) := by
  have := quasiIso_shiftedLiftShortComplex S hS
  dsimp only [liftShortComplex]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftShortComplex_fst : liftShortComplex S ≫ fst S.g = S.f := by
  ext n
  have aux (p q : ℤ) (h : p = q) (hpq : p + 0 = q) :
      (S.X₁.XIsoOfEq h.symm).hom ≫ (HomComplex.Cochain.ofHom S.f).v p q hpq =
        S.f.f q := by
    subst q
    simp
  simpa [liftShortComplex, shiftedLiftShortComplex, fst,
    shiftFunctorCompIsoId, shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    mappingCone.rotateHomotopyEquiv, mappingCone.map,
    mappingCone.lift_f _ _ _ _ (n + -1) n (by omega),
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso] using
      aux (n + -1 + 1) n (by omega) (by omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftShortComplex_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (liftShortComplex S).f p ≫ (snd S.g).v p q hpq = 0 := by
  subst q
  simp [liftShortComplex, shiftedLiftShortComplex, snd,
    shiftFunctorCompIsoId, shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    mappingCone.rotateHomotopyEquiv, mappingCone.map,
    mappingCone.lift_f _ _ _ _ (p + -1) p (by omega),
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

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
