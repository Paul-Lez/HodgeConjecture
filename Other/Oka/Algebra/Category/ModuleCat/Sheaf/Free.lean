/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Coordinates and sections of free sheaves of modules -/

@[expose] public noncomputable section

universe u v' u'

open CategoryTheory Limits

namespace PresheafOfModules

/-- Restriction maps depend only on the underlying morphism. -/
lemma map_apply_congr {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M : PresheafOfModules.{u} R} {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (x : M.obj X) :
    M.map f x = M.map g x := by
  subst h
  rfl

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf on one generator is the unit. -/
def freePUnitIso : free (R := R) PUnit.{u + 1} ≅ unit R :=
  (isColimitFreeCofan PUnit.{u + 1}).coconePointUniqueUpToIso
    (Cofan.IsColimit.mk (Cofan.mk (unit R) (fun _ ↦ 𝟙 _)) (fun s ↦ s.inj PUnit.unit)
      (fun s j ↦ by cases j; exact Category.id_comp _)
      (fun s m hm ↦ by rw [← hm PUnit.unit]; exact (Category.id_comp m).symm))

/-- The free sheaf on an empty type is zero. -/
lemma isZero_free_of_isEmpty (I : Type u) [IsEmpty I] : IsZero (free (R := R) I) :=
  (IsZero.iff_id_eq_zero _).mpr <|
    (freeHomEquiv _).injective (funext fun i ↦ (IsEmpty.false i).elim)

section Evaluation

variable {M N : SheafOfModules.{u} R} {I : Type u}

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Finite sums of morphisms act pointwise as sums. -/
lemma val_app_sum {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N)) (Z : Cᵒᵖ)
    (x : M.val.obj Z) :
    (∑ i ∈ s, φ i).val.app Z x = ∑ i ∈ s, (φ i).val.app Z x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A morphism from the unit corresponding to `s` multiplies by `s`. -/
lemma unitHomEquiv_symm_val_app (s : M.sections) (Z : Cᵒᵖ) (r : R.obj.obj Z) :
    (M.unitHomEquiv.symm s).val.app Z r = r • PresheafOfModules.sections.eval s Z :=
  rfl

variable (R) in
/-- The `i`-th projection from a free sheaf to the unit. -/
def freeProj [DecidableEq I] (i : I) : free (R := R) I ⟶ unit R :=
  Cofan.IsColimit.desc (isColimitFreeCofan I) (fun j ↦ if j = i then 𝟙 (unit R) else 0)

/-- The inclusions and projections satisfy the first dual-basis identity. -/
@[reassoc (attr := simp)]
lemma ιFree_comp_freeProj [DecidableEq I] (i j : I) :
    ιFree i ≫ freeProj R j = if i = j then 𝟙 (unit R) else 0 :=
  Cofan.IsColimit.fac (isColimitFreeCofan I) _ i

/-- For finite index types, projections followed by inclusions sum to the identity. -/
lemma sum_freeProj_comp_ιFree [Fintype I] [DecidableEq I] :
    ∑ i : I, freeProj R i ≫ ιFree (R := R) i = 𝟙 (free I) := by
  refine Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _ (fun j ↦ ?_)
  change ιFree j ≫ _ = ιFree j ≫ _
  rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [← Category.assoc, ιFree_comp_freeProj, if_neg (Ne.symm hij), Limits.zero_comp]
  · simp

variable [DecidableEq I] (Z : Cᵒᵖ)

/-- The coordinates of a section of a finite free sheaf. -/
def freeEval :
    (free (R := R) I).val.obj Z →ₗ[R.obj.obj Z] (I → R.obj.obj Z) :=
  LinearMap.pi fun i ↦ ((freeProj R i).val.app Z).hom

@[simp]
lemma freeEval_apply (b : (free (R := R) I).val.obj Z) (i : I) :
    freeEval Z b i = (freeProj R i).val.app Z b :=
  rfl

variable [Fintype I]

/-- Build a section of a finite free sheaf from its coordinates. -/
def freeEvalSymm :
    (I → R.obj.obj Z) →ₗ[R.obj.obj Z] (free (R := R) I).val.obj Z :=
  ∑ i : I, ((ιFree (R := R) i).val.app Z).hom ∘ₗ LinearMap.proj i

omit [DecidableEq I] in
lemma freeEvalSymm_apply (a : I → R.obj.obj Z) :
    freeEvalSymm (R := R) (I := I) Z a = ∑ i : I, (ιFree i).val.app Z (a i) := by
  rw [freeEvalSymm, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ rfl

@[simp]
lemma freeEval_freeEvalSymm (a : I → R.obj.obj Z) :
    freeEval Z (freeEvalSymm (R := R) (I := I) Z a) = a := by
  ext j
  rw [freeEval_apply, freeEvalSymm_apply, map_sum, Finset.sum_eq_single j]
  · change (ιFree j ≫ freeProj R j).val.app Z (a j) = a j
    rw [ιFree_comp_freeProj, if_pos rfl]
    rfl
  · intro i _ hij
    change (ιFree i ≫ freeProj R j).val.app Z (a i) = 0
    rw [ιFree_comp_freeProj, if_neg hij]
    rfl
  · simp

@[simp]
lemma freeEvalSymm_freeEval (b : (free (R := R) I).val.obj Z) :
    freeEvalSymm Z (freeEval (R := R) (I := I) Z b) = b := by
  rw [freeEvalSymm_apply]
  have : ∀ i : I, (ιFree (R := R) i).val.app Z (freeEval Z b i) =
      (freeProj R i ≫ ιFree i).val.app Z b := fun i ↦ rfl
  simp_rw [this]
  rw [← val_app_sum, sum_freeProj_comp_ιFree]
  rfl

/-- Sections of a finite free sheaf are tuples of ring sections. -/
def freeEvalEquiv :
    (free (R := R) I).val.obj Z ≃ₗ[R.obj.obj Z] (I → R.obj.obj Z) :=
  LinearEquiv.ofLinearMap (freeEval Z) (freeEvalSymm Z)
    (LinearMap.ext fun a ↦ freeEval_freeEvalSymm Z a)
    (LinearMap.ext fun b ↦ freeEvalSymm_freeEval Z b)

@[simp]
lemma freeEvalEquiv_apply (b : (free (R := R) I).val.obj Z) :
    freeEvalEquiv Z b = freeEval Z b :=
  rfl

@[simp]
lemma freeEvalEquiv_symm_apply (a : I → R.obj.obj Z) :
    (freeEvalEquiv (R := R) (I := I) Z).symm a = freeEvalSymm Z a :=
  rfl

omit [Fintype I] in
lemma freeEval_injective [Finite I] : Function.Injective (freeEval (R := R) (I := I) Z) := by
  let _ := Fintype.ofFinite I
  exact (freeEvalEquiv Z).injective

omit [Fintype I] in
lemma freeEval_naturality {Z W : Cᵒᵖ} (f : Z ⟶ W) (b : (free (R := R) I).val.obj Z) (i : I) :
    freeEval W ((free (R := R) I).val.map f b) i = R.obj.map f (freeEval Z b i) :=
  PresheafOfModules.naturality_apply (freeProj R i).val f b

omit [DecidableEq I] in
lemma map_freeEvalSymm {Z W : Cᵒᵖ} (f : Z ⟶ W) (a : I → R.obj.obj Z) :
    (free (R := R) I).val.map f (freeEvalSymm Z a) =
      freeEvalSymm W (fun i ↦ R.obj.map f (a i)) := by
  classical
  refine freeEval_injective W (funext fun i ↦ ?_)
  rw [freeEval_naturality, freeEval_freeEvalSymm, freeEval_freeEvalSymm]

/-- Evaluate a morphism from a finite free sheaf in coordinates. -/
lemma val_app_eq_sum (φ : free (R := R) I ⟶ M) (b : (free (R := R) I).val.obj Z) :
    φ.val.app Z b =
      ∑ i : I, freeEval Z b i • PresheafOfModules.sections.eval (M.freeHomEquiv φ i) Z := by
  conv_lhs => rw [← freeEvalSymm_freeEval Z b, freeEvalSymm_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  change (ιFree i ≫ φ).val.app Z (freeEval Z b i) = _
  rw [← unitHomEquiv_symm_freeHomEquiv_apply φ i, unitHomEquiv_symm_val_app]

end Evaluation

section Sections

variable {T : C} (hT : IsTerminal T) (M : SheafOfModules.{u} R)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Construct a section from its value at a terminal object. -/
def sectionOfTerminal (b : M.val.obj (Opposite.op T)) : M.sections :=
  PresheafOfModules.sectionsMk (fun Z ↦ M.val.map (hT.from Z.unop).op b) (fun {Z W} f ↦ by
    rw [← PresheafOfModules.map_comp_apply]
    exact PresheafOfModules.map_apply_congr (Quiver.Hom.unop_inj (hT.hom_ext _ _)) b)

@[simp]
lemma sectionOfTerminal_val (b : M.val.obj (Opposite.op T)) (Z : Cᵒᵖ) :
    PresheafOfModules.sections.eval (sectionOfTerminal hT M b) Z =
      M.val.map (hT.from Z.unop).op b :=
  rfl

@[simp]
lemma sectionOfTerminal_eval (s : M.sections) :
    sectionOfTerminal hT M (PresheafOfModules.sections.eval s (Opposite.op T)) = s := by
  ext Z
  exact PresheafOfModules.sections_property s (hT.from Z.unop).op

variable {M} in
lemma sectionsMap_sectionOfTerminal {N : SheafOfModules.{u} R} (p : M ⟶ N)
    (b : M.val.obj (Opposite.op T)) :
    sectionsMap p (sectionOfTerminal hT M b) =
      sectionOfTerminal hT N (p.val.app (Opposite.op T) b) := by
  ext Z
  exact PresheafOfModules.naturality_apply p.val (hT.from Z.unop).op b

end Sections


end SheafOfModules
