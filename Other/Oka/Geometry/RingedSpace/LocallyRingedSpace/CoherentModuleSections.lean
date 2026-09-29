/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModule
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.LocallySurjective

/-!
# Local generators and local relations of coherent sheaves of modules

Let `M` be a sheaf of `𝒪_Y`-modules on a locally ringed space `Y`. This file proves the converse
of `AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_hasLocalModuleRelations`:

* if `M` is of finite type, it is locally finitely generated on sections
  (`AlgebraicGeometry.LocallyRingedSpace.isLocallyFinitelyGeneratedModule_of_isFiniteType`);
* if `M` is coherent, every finite family of sections has locally finitely generated relations
  (`AlgebraicGeometry.LocallyRingedSpace.hasLocalModuleRelations_of_isCoherent`).

Both are read off from the definitions: a finite family of generating sections of `M.over W` is
an epimorphism `free I ⟶ M.over W`, hence locally surjective on sections, and the relations
between sections `f₁, …, f_m` over `V` are the sections of the kernel of the corresponding
morphism `free (Fin m) ⟶ M.over V`, which is of finite type when `M` is coherent.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite SheafOfModules AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {P Q : SheafOfModules.{u} R}

/-- **A section killed by `φ` is a section of the kernel of `φ`.** -/
lemma exists_kernel_ι_val_app_eq (φ : P ⟶ Q) (Z : Cᵒᵖ) (b : P.val.obj Z)
    (hb : φ.val.app Z b = 0) : ∃ n, (kernel.ι φ).val.app Z n = b := by
  let E := evaluation R Z
  haveI : E.Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  let e := PreservesKernel.iso E φ
  let k := (ModuleCat.kernelIsoKer (E.map φ)).inv ⟨b, hb⟩
  refine ⟨e.inv k, ?_⟩
  have h1 : E.map (kernel.ι φ) (e.inv k) = kernel.ι (E.map φ) k := by
    rw [← ConcreteCategory.comp_apply]
    congr 1
    simp [e]
  have h2 : kernel.ι (E.map φ) k = b := by
    change ((ModuleCat.kernelIsoKer (E.map φ)).inv ≫ kernel.ι (E.map φ)) ⟨b, hb⟩ = b
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  exact h1.trans h2

section Generators

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Local generators of a sheaf of modules of finite type, on sections**: there is a family of
objects covering the terminal object, and over each of them finitely many sections, such that
every section over an object `Z` mapping to a member `X a` of the family is, on a covering sieve
of `Z`, a linear combination of the restrictions of the sections over `X a`. -/
lemma IsFiniteType.exists_sections (K : SheafOfModules.{u} R) [K.IsFiniteType] :
    ∃ (A : Type u) (X : A → C) (_ : J.CoversTop X) (k : A → ℕ)
      (s : ∀ a, Fin (k a) → K.val.obj (op (X a))),
      ∀ (a : A) (Z : C) (h : Z ⟶ X a) (n : K.val.obj (op Z)), ∃ S : Sieve Z, S ∈ J Z ∧
        ∀ ⦃W : C⦄ (g : W ⟶ Z), S g → ∃ c : Fin (k a) → R.obj.obj (op W),
          K.val.map g.op n = ∑ l, c l • K.val.map (g ≫ h).op (s a l) := by
  classical
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u} K
  obtain ⟨hfin⟩ := hσ
  have hk : ∀ a, ∃ k : ℕ, Nonempty ((σ.generators a).I ≃ Fin k) := fun a ↦
    @Finite.exists_equiv_fin _ (hfin a).finite
  choose k e using hk
  refine ⟨σ.I, σ.X, σ.coversTop, k, fun a l ↦ PresheafOfModules.sections.eval
    ((K.over (σ.X a)).freeHomEquiv (σ.generators a).π ((e a).some.symm l))
      (op (Over.mk (𝟙 (σ.X a)))), fun a Z h n ↦ ?_⟩
  let G := σ.generators a
  haveI : Fintype G.I := @Fintype.ofFinite _ (hfin a).finite
  obtain ⟨S, hS, hS'⟩ := SheafOfModules.exists_app_eq_of_epi G.π (Over.mk h) n
  rw [GrothendieckTopology.mem_over_iff] at hS
  refine ⟨_, hS, fun W g hg ↦ ?_⟩
  rw [Sieve.overEquiv_iff] at hg
  obtain ⟨c, hc⟩ := hS' _ hg
  refine ⟨fun l ↦ freeEval (R := R.over (σ.X a)) _ c ((e a).some.symm l), ?_⟩
  have h1 := val_app_eq_sum (R := R.over (σ.X a)) _ G.π c
  refine (hc.symm.trans h1).trans ?_
  refine Fintype.sum_equiv (e a).some _ _ (fun j ↦ ?_)
  simp only [Equiv.symm_apply_apply]
  congr 1
  exact (PresheafOfModules.sections_property ((K.over (σ.X a)).freeHomEquiv G.π j)
    (Over.homMk (g ≫ h) (Category.comp_id _) :
      Over.mk (g ≫ h) ⟶ Over.mk (𝟙 (σ.X a))).op).symm

end Generators

end SheafOfModules

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}} (M : SheafOfModules.{u} Y.ringSheaf)

/-- A point of `X` lies in a member of a family covering the terminal object of the slice site
over `X`. -/
lemma exists_mem_of_coversTop_over {X : Opens Y} {A : Type*} {Z : A → Over X}
    (hZ : ((Opens.grothendieckTopology Y).over X).CoversTop Z) (x : Y) (hx : x ∈ X) :
    ∃ a, x ∈ (Z a).left := by
  have h := hZ (Over.mk (𝟙 X))
  rw [GrothendieckTopology.mem_over_iff] at h
  obtain ⟨W, g, hg, hxW⟩ := h x hx
  rw [Sieve.overEquiv_iff] at hg
  obtain ⟨a, ⟨k⟩⟩ := hg
  exact ⟨a, leOfHom k.left hxW⟩

/-- **A sheaf of modules of finite type is locally finitely generated on sections.** -/
theorem isLocallyFinitelyGeneratedModule_of_isFiniteType [M.IsFiniteType] :
    IsLocallyFinitelyGeneratedModule M := by
  obtain ⟨A, X, hX, k, s, hs⟩ := SheafOfModules.IsFiniteType.exists_sections M
  have hcov : IsOpenCover X := (Opens.coversTop_iff _ X).1 hX
  intro x
  obtain ⟨a, ha⟩ : ∃ a, x ∈ X a := by
    have : x ∈ (⊤ : Opens Y.toPresheafedSpace) := trivial
    rw [← hcov.iSup_eq_top] at this
    exact Opens.mem_iSup.1 this
  refine ⟨X a, k a, s a, ha, fun W' hW' t y hy ↦ ?_⟩
  obtain ⟨S, hS, hS'⟩ := hs a W' (homOfLE hW') t
  obtain ⟨W'', g, hg, hyW''⟩ := hS y hy
  obtain ⟨c, hc⟩ := hS' g hg
  exact ⟨W'', leOfHom g, hyW'', c, hc⟩

set_option maxHeartbeats 400000 in
-- sections of the sheaves of modules on the slice site are identified with sections of `M` and
-- of `𝒪_Y` by unfolding, which is slow
/-- **A coherent sheaf of modules has locally finitely generated relations on sections.** -/
theorem hasLocalModuleRelations_of_isCoherent [M.IsCoherent] : HasLocalModuleRelations M := by
  classical
  intro V m f x hx
  let L := ULift.{u} (Fin m)
  let φ : free L ⟶ M.over V := (M.over V).freeHomEquiv.symm
    (fun i ↦ sectionOfTerminal Over.mkIdTerminal (M.over V) (f i.down))
  have key : ∀ (Z : Over V) (b : (free (R := Y.ringSheaf.over V) L).val.obj (op Z)),
      φ.val.app (op Z) b = ∑ i : Fin m, (show Y.presheaf.obj (op Z.left) from
        freeEval (R := Y.ringSheaf.over V) (op Z) b (ULift.up i)) •
        sectRes M (leOfHom Z.hom) (f i) := by
    intro Z b
    rw [val_app_eq_sum]
    refine Fintype.sum_equiv Equiv.ulift _ _ (fun i ↦ ?_)
    simp only [φ, Equiv.apply_symm_apply, sectionOfTerminal_val]
    rfl
  obtain ⟨K, ι, hι, hlift, hK⟩ : ∃ (K : SheafOfModules.{u} (Y.ringSheaf.over V))
      (ι : K ⟶ free L),
      (∀ (Z : (Over V)ᵒᵖ) (n : K.val.obj Z), φ.val.app Z (ι.val.app Z n) = 0) ∧
      (∀ (Z : (Over V)ᵒᵖ) (b : (free (R := Y.ringSheaf.over V) L).val.obj Z),
        φ.val.app Z b = 0 → ∃ n, ι.val.app Z n = b) ∧ K.IsFiniteType :=
    ⟨kernel φ, kernel.ι φ, val_app_apply_eq_zero_of_mem_kernel φ,
      exists_kernel_ι_val_app_eq φ, IsCoherent.isFiniteType_kernel φ⟩
  obtain ⟨A, X, hX, k, s, hs⟩ := SheafOfModules.IsFiniteType.exists_sections K
  obtain ⟨a, ha⟩ := exists_mem_of_coversTop_over hX x hx
  let g : Fin (k a) → Fin m → Y.presheaf.obj (op (X a).left) := fun l i ↦
    freeEval (R := Y.ringSheaf.over V) (op (X a)) (ι.val.app _ (s a l)) (ULift.up i)
  refine ⟨(X a).left, leOfHom (X a).hom, k a, g, ha, fun l ↦ ?_, ?_⟩
  · exact (key (X a) _).symm.trans (hι (op (X a)) (s a l))
  intro W' hW' a' hrel y hy
  let Z' : Over V := Over.mk (homOfLE (hW'.trans (leOfHom (X a).hom)))
  let b := freeEvalSymm (R := Y.ringSheaf.over V) (I := L) (op Z') (fun i ↦ a' i.down)
  have hb : φ.val.app (op Z') b = 0 := by
    refine (key Z' b).trans (Eq.trans ?_ hrel)
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    simp only [b, freeEval_freeEvalSymm]
  obtain ⟨n, hn⟩ := hlift (op Z') b hb
  obtain ⟨S, hS, hS'⟩ := hs a Z' (Over.homMk (homOfLE hW') (Subsingleton.elim _ _)) n
  rw [GrothendieckTopology.mem_over_iff] at hS
  obtain ⟨W'', gg, hgg, hyW''⟩ := hS y hy
  rw [Sieve.overEquiv_iff] at hgg
  obtain ⟨c, hc⟩ := hS' _ hgg
  refine ⟨W'', leOfHom gg, hyW'', c, fun i ↦ ?_⟩
  have h2 := congrArg (fun t ↦ freeEval (R := Y.ringSheaf.over V) (I := L) (op (Over.mk
    (gg ≫ Z'.hom))) (ι.val.app _ t) (ULift.up i)) hc
  simp only at h2
  rw [PresheafOfModules.naturality_apply] at h2
  erw [hn] at h2
  rw [freeEval_naturality] at h2
  simp only [b, freeEval_freeEvalSymm] at h2
  have hR : ∀ (Z : (Over V)ᵒᵖ) (c : Fin (k a) → (Y.ringSheaf.over V).obj.obj Z)
      (v : Fin (k a) → K.val.obj Z),
      freeEval (R := Y.ringSheaf.over V) (I := L) Z (ι.val.app Z (∑ x, c x • v x))
        (ULift.up i) =
        ∑ x, c x * freeEval (R := Y.ringSheaf.over V) (I := L) Z (ι.val.app Z (v x))
          (ULift.up i) := by
    intro Z c v
    rw [map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    rw [map_smul, map_smul]
    rfl
  refine h2.trans ((hR _ c _).trans (Finset.sum_congr rfl (fun l _ ↦ ?_)))
  congr 1
  rw [PresheafOfModules.naturality_apply, freeEval_naturality]
  rfl

end AlgebraicGeometry.LocallyRingedSpace

end
