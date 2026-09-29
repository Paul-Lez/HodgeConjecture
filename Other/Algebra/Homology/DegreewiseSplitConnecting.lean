/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# The connecting map of a degreewise split sequence

The degree-one cocycle associated to a degreewise splitting induces the standard
connecting morphism in the long exact homology sequence, with positive sign.
This identifies its value on cycles directly with the snake-lemma normalization.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type*} [Category* C] [Abelian C]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The split connecting cocycle induces the usual long-exact-sequence boundary. -/
theorem homology_shiftMap_homOfDegreewiseSplit_eq_δ (hS : S.ShortExact) (n m : ℤ) (h : n + 1 = m) :
    (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
      (homOfDegreewiseSplit S σ) n m (by omega) =
      hS.δ n m h := by
  subst m
  let x₃ := S.X₃.iCycles n
  let x₂ := x₃ ≫ (σ n).s
  let x₁ := x₂ ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r
  have hx₃ : x₃ ≫ S.X₃.d n (n + 1) = 0 := S.X₃.iCycles_d _ _
  have hx₂ : x₂ ≫ S.g.f n = x₃ := by
    dsimp [x₂]
    erw [Category.assoc, (σ n).s_g]
    exact Category.comp_id _
  have hx₁ : x₁ ≫ S.f.f (n + 1) = x₂ ≫ S.X₂.d n (n + 1) := by
    change (x₂ ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r) ≫ S.f.f (n + 1) = _
    have hr := (σ (n + 1)).r_f
    dsimp only [ShortComplex.map, HomologicalComplex.eval] at hr
    simp only [Category.assoc]
    simp only [hr, Preadditive.comp_sub, Category.comp_id]
    rw [← S.g.comm_assoc, ← Category.assoc x₂, hx₂,
      ← Category.assoc x₃, hx₃, zero_comp, sub_zero]
  have hδ := hS.δ_eq n (n + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ (n + 2) (by simp; omega)
  have hi : S.X₃.liftCycles x₃ (n + 1) (by simp) hx₃ = 𝟙 _ := by
    apply (cancel_mono (S.X₃.iCycles n)).1
    simp only [HomologicalComplex.liftCycles_i, Category.id_comp]
    rfl
  rw [hi, Category.id_comp] at hδ
  rw [← cancel_epi (S.X₃.homologyπ n), hδ]
  conv_lhs => rw [← Category.id_comp (S.X₃.homologyπ n), ← hi]
  dsimp [Functor.shiftMap, homologyFunctor_shift]
  rw [Category.assoc]
  erw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    S.X₁.liftCycles_shift_homologyπ_assoc _ _ _ _ (n + 1) (by omega) (n + 2) (by simp; omega)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id (S.X₁.homologyπ (n + 1))]
  apply congrArg (fun f : S.X₃.cycles n ⟶ S.X₁.cycles (n + 1) => f ≫ S.X₁.homologyπ (n + 1))
  apply (cancel_mono (S.X₁.iCycles (n + 1))).1
  simp only [HomologicalComplex.liftCycles_i]
  simp only [homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit,
    HomComplex.Cocycle.mk_coe, HomComplex.Cochain.mk_v, shiftFunctorObjXIso]
  dsimp only [x₁, x₂, HomologicalComplex.XIsoOfEq]
  simp [eqToIso, Category.assoc]
end CochainComplex
