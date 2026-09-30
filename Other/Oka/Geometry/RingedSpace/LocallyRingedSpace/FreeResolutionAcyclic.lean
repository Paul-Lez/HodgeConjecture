/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Free
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.FreeResolution
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CohomologyRestrict
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalk
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.OpenImmersionCohomology
public import Other.Oka.Topology.Sheaves.Cohomology.Cech
public import Other.Oka.Topology.Sheaves.Cohomology.Leray
public import Other.Oka.Topology.Sheaves.Cohomology.Vanishing

/-!
# Acyclicity of sheaves with a finite free resolution

Let `Y` be a locally ringed space and `W` an open on which the structure sheaf is acyclic,
`Hᵠ(W, 𝒪_Y) = 0` for `q ≥ 1`. If a sheaf of modules `M` has a finite free resolution
(`SheafOfModules.HasFreeResolutionLE`), then `Hᵠ(W, M) = 0` for `q ≥ 1` (dimension shifting),
and the first two steps `𝒪^{I'} ⟶ 𝒪^I ⟶ M ⟶ 0` of the resolution stay exact on sections over
`W`.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.subsingleton_H_restrictOpen_free`: finite free sheaves
  are acyclic on `W`.
- `SheafOfModules.HasFreeResolutionLE.exists_presentation_acyclic`: a finite free resolution
  gives a presentation `𝒪^{I'} ⟶ 𝒪^I ⟶ M` which is exact on sections over every `W` on which
  `𝒪_Y` is acyclic, and `M` is acyclic on such `W`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

section Free

variable {I : Type u} [Finite I]

/-- **Finite free sheaves are acyclic** on every open on which the structure sheaf is. -/
lemma subsingleton_H_restrictOpen_free (W : Opens Y.toPresheafedSpace)
    (hW : ∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen W).obj Y.structureSheafAb) q)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj
      (SheafOfModules.free (R := Y.ringSheaf) I).toAb) q) := by
  classical
  have := Fintype.ofFinite I
  let F := modulesToAb Y ⋙ TopCat.Sheaf.restrictOpen W
  refine TopCat.Sheaf.subsingleton_H_of_sum Finset.univ
    (fun _ : I ↦ F.obj (SheafOfModules.unit Y.ringSheaf))
    (fun i ↦ F.map (SheafOfModules.freeProj _ i)) (fun i ↦ F.map (SheafOfModules.ιFree i)) ?_ q
    (fun _ _ ↦ hW q hq)
  simp_rw [← F.map_comp, ← F.map_sum, SheafOfModules.sum_freeProj_comp_ιFree, F.map_id]

end Free

end AlgebraicGeometry.LocallyRingedSpace

namespace SheafOfModules.HasFreeResolutionLE

open AlgebraicGeometry LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

/-- **A finite free resolution gives a presentation which is exact on acyclic opens.** If `M` has
a finite free resolution, there is a presentation `𝒪^{I'} ⟶ 𝒪^I ⟶ M` such that for every open
`W` on which `𝒪_Y` is acyclic, `M` is acyclic on `W`, `𝒪(W)^I ⟶ M(W)` is surjective and its
kernel is the image of `𝒪(W)^{I'}`. -/
theorem exists_presentation_acyclic {M : SheafOfModules.{u} Y.ringSheaf} {d : ℕ}
    (h : M.HasFreeResolutionLE d) :
    ∃ (I I' : Type u) (_ : Finite I) (_ : Finite I') (p : SheafOfModules.free I ⟶ M)
      (a : SheafOfModules.free I' ⟶ SheafOfModules.free I), a ≫ p = 0 ∧
      ∀ W : Opens Y.toPresheafedSpace,
        (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
          ((TopCat.Sheaf.restrictOpen W).obj Y.structureSheafAb) q)) →
        (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
          ((TopCat.Sheaf.restrictOpen W).obj M.toAb) q)) ∧
        Function.Surjective (p.val.app (op W)) ∧
        ∀ t, p.val.app (op W) t = 0 → ∃ t', a.val.app (op W) t' = t := by
  induction h with
  | free n I e =>
    refine ⟨I, PEmpty, inferInstance, inferInstance, e.inv, 0, by simp, fun W hW ↦
      ⟨fun q hq ↦ ?_, ?_, fun t ht ↦ ⟨0, ?_⟩⟩⟩
    · haveI := subsingleton_H_restrictOpen_free W hW q hq (I := I)
      exact TopCat.Sheaf.subsingleton_H_of_iso
        ((TopCat.Sheaf.restrictOpen W).mapIso ((modulesToAb Y).mapIso e)) q
    · intro s
      refine ⟨e.hom.val.app (op W) s, ?_⟩
      change (e.hom ≫ e.inv).val.app (op W) s = s
      rw [e.hom_inv_id]
      rfl
    · have ht0 : t = 0 := by
        have : t = (e.inv ≫ e.hom).val.app (op W) t := by rw [e.inv_hom_id]; rfl
        rw [this, SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, ht,
          map_zero]
      rw [ht0]
      exact map_zero _
  | @ext M K n I _ i p w hS hK ih =>
    obtain ⟨I₂, I₂', _, _, p₂, a₂, hpa₂, H₂⟩ := ih
    refine ⟨I, I₂, inferInstance, inferInstance, p, p₂ ≫ i, by simp [w], fun W hW ↦ ?_⟩
    obtain ⟨hK₁, hK₂, -⟩ := H₂ W hW
    have hS' := shortExact_map_modulesToAb hS
    have hSW := TopCat.Sheaf.shortExact_restrictOpen W hS'
    refine ⟨fun q hq ↦ ?_, ?_, fun t ht ↦ ?_⟩
    · exact @TopCat.Sheaf.subsingleton_H_X₃_of_shortExact _ _ hSW q
        (subsingleton_H_restrictOpen_free W hW q hq (I := I)) (hK₁ (q + 1) (by omega))
    · exact TopCat.Sheaf.surjective_of_H_one_restrictOpen W hS'
        (fun x ↦ @Subsingleton.elim _ (hK₁ 1 one_pos) x 0)
    · obtain ⟨k, hk⟩ := (TopCat.Presheaf.sections_exact hS' W).2 t ht
      obtain ⟨t', rfl⟩ := hK₂ k
      exact ⟨t', hk⟩

end SheafOfModules.HasFreeResolutionLE

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-- The preimage in the open subspace `X|_N` of an open `W ≤ N` of `X`. -/
def preimageOpen (N : Opens X.toPresheafedSpace) (W : Opens X.toPresheafedSpace) :
    Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace :=
  (Opens.map N.inclusion').obj W

/-- The image of the preimage of `W ≤ N` is `W`. -/
lemma functor_obj_preimageOpen {N W : Opens X.toPresheafedSpace} (hW : W ≤ N) :
    N.isOpenEmbedding.isOpenMap.functor.obj (preimageOpen N W) = W := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨⟨x, hW hx⟩, hx, rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact hy

/-- Two restrictions of a section of a presheaf of modules on opens compose. -/
lemma sheafOfModules_map_map {X : LocallyRingedSpace.{u}} (M : SheafOfModules.{u} X.ringSheaf)
    {U V W : Opens X.toPresheafedSpace} (h₁ : W ≤ V) (h₂ : V ≤ U) (s : M.val.obj (op U)) :
    M.val.map (homOfLE h₁).op (M.val.map (homOfLE h₂).op s) =
      M.val.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- Restriction of a section of a presheaf of modules along an equality of opens is the
identity. -/
lemma sheafOfModules_map_self {X : LocallyRingedSpace.{u}} (M : SheafOfModules.{u} X.ringSheaf)
    {U : Opens X.toPresheafedSpace} (h : U ≤ U) (s : M.val.obj (op U)) :
    M.val.map (homOfLE h).op s = s := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, PresheafOfModules.map_id]
  rfl

/-- Restriction of a linear combination of sections of a sheaf of modules. -/
lemma sheafOfModules_map_sum_smul {X : LocallyRingedSpace.{u}}
    (M : SheafOfModules.{u} X.ringSheaf) {U W : Opens X.toPresheafedSpace} (h : W ≤ U)
    {I : Type*} (s : Finset I) (r : I → X.ringSheaf.obj.obj (op U)) (σ : I → M.val.obj (op U)) :
    M.val.map (homOfLE h).op (∑ i ∈ s, r i • σ i) =
      ∑ i ∈ s, X.ringSheaf.obj.map (homOfLE h).op (r i) • M.val.map (homOfLE h).op (σ i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ PresheafOfModules.map_smul _ _ _ _

/-- Two restrictions of a section of the structure sheaf compose. -/
lemma ringSheaf_map_map {X : LocallyRingedSpace.{u}}
    {U V W : Opens X.toPresheafedSpace} (h₁ : W ≤ V) (h₂ : V ≤ U) (s : X.ringSheaf.obj.obj (op U)) :
    X.ringSheaf.obj.map (homOfLE h₁).op (X.ringSheaf.obj.map (homOfLE h₂).op s) =
      X.ringSheaf.obj.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← RingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of a section of the structure sheaf along an equality of opens is the
identity. -/
lemma ringSheaf_map_self {X : LocallyRingedSpace.{u}}
    {U : Opens X.toPresheafedSpace} (h : U ≤ U) (s : X.ringSheaf.obj.obj (op U)) :
    X.ringSheaf.obj.map (homOfLE h).op s = s := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- The coordinates of the image of a section under a morphism of finite free sheaves, in terms
of the coordinates of the images of the generators. -/
lemma freeEval_val_app_free {Y : LocallyRingedSpace.{u}} {I I' : Type u}
    [Fintype I'] [DecidableEq I] [DecidableEq I']
    (a : SheafOfModules.free (R := Y.ringSheaf) I' ⟶ SheafOfModules.free I)
    (W : Opens Y.toPresheafedSpace) (t : (SheafOfModules.free (R := Y.ringSheaf) I').val.obj (op W))
    (i : I) :
    SheafOfModules.freeEval (op W) (a.val.app (op W) t) i = ∑ j,
      SheafOfModules.freeEval (op W) t j * Y.ringSheaf.obj.map (homOfLE le_top : W ⟶ ⊤).op
        (SheafOfModules.freeEval (op ⊤) (a.val.app (op ⊤) (generatorSection (𝟙 _) j)) i) := by
  rw [SheafOfModules.val_app_eq_sum (op W) a t, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, eval_freeHomEquiv_eq_map]
  erw [SheafOfModules.freeEval_naturality]
  congr 3

variable (N : Opens X.toPresheafedSpace) (M : SheafOfModules.{u} X.ringSheaf) {I : Type u}

/-- The sections of `M|_N = (restrictOverEquiv X N).functor.obj (M.over N)` over an open `W'` of
`X|_N` are the sections of `M` over the image of `W'`. -/
noncomputable def restrictSectionsEquiv
    (W' : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace) :
    ((restrictOverEquiv X N).functor.obj (M.over N)).val.obj (op W') ≃+
      M.val.obj (op (N.isOpenEmbedding.isOpenMap.functor.obj W')) :=
  AddEquiv.refl _

variable {N M}

/-- `AlgebraicGeometry.LocallyRingedSpace.restrictSectionsEquiv` is linear. -/
lemma restrictSectionsEquiv_smul (W' : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace)
    (r : (X.restrict N.isOpenEmbedding).ringSheaf.obj.obj (op W'))
    (m : ((restrictOverEquiv X N).functor.obj (M.over N)).val.obj (op W')) :
    restrictSectionsEquiv N M W' (r • m) =
      (show X.ringSheaf.obj.obj (op (N.isOpenEmbedding.isOpenMap.functor.obj W')) from r) •
        restrictSectionsEquiv N M W' m :=
  rfl

/-- `AlgebraicGeometry.LocallyRingedSpace.restrictSectionsEquiv` commutes with restriction. -/
lemma restrictSectionsEquiv_map {W'₁ W'₂ : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace}
    (h : W'₁ ≤ W'₂) (h' : N.isOpenEmbedding.isOpenMap.functor.obj W'₁ ≤
      N.isOpenEmbedding.isOpenMap.functor.obj W'₂)
    (m : ((restrictOverEquiv X N).functor.obj (M.over N)).val.obj (op W'₂)) :
    restrictSectionsEquiv N M W'₁
        (((restrictOverEquiv X N).functor.obj (M.over N)).val.map (homOfLE h).op m) =
      M.val.map (homOfLE h').op (restrictSectionsEquiv N M W'₂ m) :=
  rfl

variable (N M)

/-- The value on `N` of the `i`-th generator of a morphism `𝒪^I ⟶ M|_N` on the open subspace
`X|_N`, a section of `M` over `N`. -/
noncomputable def restrictGenerator
    (p : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I ⟶
      (restrictOverEquiv X N).functor.obj (M.over N)) (i : I) : M.val.obj (op N) :=
  M.val.map (homOfLE (TopCat.Sheaf.functor_obj_top N).ge).op
    (restrictSectionsEquiv N M ⊤ (generatorSection p i))

variable {N M}

/-- The underlying abelian sheaf of `M|_N` is the restriction of that of `M`. -/
lemma restrictOverEquiv_toAb :
    ((restrictOverEquiv X N).functor.obj (M.over N)).toAb =
      (TopCat.Sheaf.restrictOpen N).obj M.toAb :=
  rfl

/-- Acyclicity of `M|_N` on an open `W'` of `X|_N` is acyclicity of `M` on its image. -/
lemma subsingleton_H_restrictOpen_of_restrict
    {W' : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace} {W : Opens X.toPresheafedSpace}
    (hφW : N.isOpenEmbedding.isOpenMap.functor.obj W' = W) {q : ℕ}
    (h : Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W').obj
      ((restrictOverEquiv X N).functor.obj (M.over N)).toAb) q)) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj M.toAb) q) := by
  rw [restrictOverEquiv_toAb] at h
  exact @Equiv.subsingleton _ _ (TopCat.Sheaf.H.restrictOpenAddEquivOfEq N.isOpenEmbedding W'
    M.toAb q hφW).toEquiv h

/-- The image of a section of `𝒪^I` over an open of `X|_N` under `p : 𝒪^I ⟶ M|_N`, read on the
corresponding open `W` of `X`, is the combination of the restricted generators. -/
lemma map_val_app_free_eq_sum [Fintype I] [DecidableEq I]
    (p : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I ⟶
      (restrictOverEquiv X N).functor.obj (M.over N))
    {W' : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace} {W : Opens X.toPresheafedSpace}
    (hφW : N.isOpenEmbedding.isOpenMap.functor.obj W' = W) (hW : W ≤ N)
    (t : (SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I).val.obj
      (op W')) :
    M.val.map (homOfLE hφW.ge).op (restrictSectionsEquiv N M W' (p.val.app (op W') t)) = ∑ i,
      X.ringSheaf.obj.map (homOfLE hφW.ge).op (SheafOfModules.freeEval (op W') t i) •
        M.val.map (homOfLE hW).op (restrictGenerator N M p i) := by
  have r₃ : N.isOpenEmbedding.isOpenMap.functor.obj W' ≤
      N.isOpenEmbedding.isOpenMap.functor.obj ⊤ :=
    hφW.le.trans (hW.trans (TopCat.Sheaf.functor_obj_top N).ge)
  rw [SheafOfModules.val_app_eq_sum (op W') p t, map_sum]
  simp_rw [restrictSectionsEquiv_smul]
  rw [sheafOfModules_map_sum_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_freeHomEquiv_eq_map]
  erw [restrictSectionsEquiv_map le_top r₃]
  rw [sheafOfModules_map_map, restrictGenerator, sheafOfModules_map_map]
  rfl

/-- Restriction of sections of a sheaf of modules along an equality of opens is injective. -/
lemma sheafOfModules_map_injective {X : LocallyRingedSpace.{u}}
    (M : SheafOfModules.{u} X.ringSheaf) {U V : Opens X.toPresheafedSpace} (h₁ : U ≤ V)
    (h₂ : V ≤ U) : Function.Injective (M.val.map (homOfLE h₁).op) := fun x y hxy ↦ by
  rw [← sheafOfModules_map_self M (le_refl V) x, ← sheafOfModules_map_self M (le_refl V) y,
    ← sheafOfModules_map_map M h₂ h₁, ← sheafOfModules_map_map M h₂ h₁, hxy]

variable (N) in
/-- The coefficients on `N` of the images of the generators under a morphism `𝒪^{I'} ⟶ 𝒪^I` of
finite free sheaves on the open subspace `X|_N`. -/
noncomputable def restrictRelation {I I' : Type u} [DecidableEq I]
    (a : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I' ⟶
      SheafOfModules.free I) (j : I') (i : I) : X.ringSheaf.obj.obj (op N) :=
  X.ringSheaf.obj.map (homOfLE (TopCat.Sheaf.functor_obj_top N).ge).op
    (SheafOfModules.freeEval (op ⊤) (a.val.app (op ⊤) (generatorSection (𝟙 _) j)) i)

/-- The relations: if `a ≫ p = 0`, the rows of the coefficient matrix of `a` are relations
between the restricted generators of `p`. -/
lemma sum_restrictRelation_smul [Fintype I] [DecidableEq I] {I' : Type u}
    (p : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I ⟶
      (restrictOverEquiv X N).functor.obj (M.over N))
    (a : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I' ⟶
      SheafOfModules.free I) (hap : a ≫ p = 0) (j : I') :
    ∑ i, restrictRelation N a j i • restrictGenerator N M p i = 0 := by
  have hz : p.val.app (op ⊤) (a.val.app (op ⊤) (generatorSection (𝟙 _) j)) = 0 := by
    change (a ≫ p).val.app (op ⊤) _ = 0
    rw [hap]
    rfl
  have h₀ := map_val_app_free_eq_sum p (TopCat.Sheaf.functor_obj_top N) le_rfl
    (a.val.app (op ⊤) (generatorSection (𝟙 _) j))
  erw [hz, map_zero] at h₀
  refine Eq.trans ?_ h₀.symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [sheafOfModules_map_self]
  rfl

/-- A relation `∑ᵢ fᵢ • gᵢ|_W = 0` between the restricted generators of `p` lifts to a section
of the kernel of `p` over the preimage `W'` of `W`. -/
lemma val_app_freeEvalSymm_eq_zero [Fintype I]
    (p : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I ⟶
      (restrictOverEquiv X N).functor.obj (M.over N))
    {W' : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace} {W : Opens X.toPresheafedSpace}
    (hφW : N.isOpenEmbedding.isOpenMap.functor.obj W' = W) (hW : W ≤ N)
    (f : I → X.ringSheaf.obj.obj (op W))
    (hf : ∑ i, f i • M.val.map (homOfLE hW).op (restrictGenerator N M p i) = 0) :
    p.val.app (op W') (SheafOfModules.freeEvalSymm (R := (X.restrict N.isOpenEmbedding).ringSheaf)
      (op W') (fun i ↦ X.ringSheaf.obj.map (homOfLE hφW.le).op (f i))) = 0 := by
  classical
  apply (restrictSectionsEquiv N M W').injective
  apply sheafOfModules_map_injective M hφW.ge hφW.le
  have h1 := map_val_app_free_eq_sum p hφW hW (SheafOfModules.freeEvalSymm
    (R := (X.restrict N.isOpenEmbedding).ringSheaf) (op W')
    (fun i ↦ X.ringSheaf.obj.map (homOfLE hφW.le).op (f i)))
  simp_rw [SheafOfModules.freeEval_freeEvalSymm, ringSheaf_map_map, ringSheaf_map_self] at h1
  rw [hf] at h1
  rw [h1, map_zero, map_zero]
  rfl

/-- A relation `∑ᵢ fᵢ • gᵢ|_W = 0` between the restricted generators of `p`, on an open `W` on
whose preimage `W'` the kernel of `p` is the image of `a`, is a combination of the rows of the
coefficient matrix of `a`. -/
lemma exists_eq_sum_restrictRelation [Fintype I] [DecidableEq I] {I' : Type u} [Fintype I']
    (p : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I ⟶
      (restrictOverEquiv X N).functor.obj (M.over N))
    (a : SheafOfModules.free (R := (X.restrict N.isOpenEmbedding).ringSheaf) I' ⟶
      SheafOfModules.free I)
    {W' : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace} {W : Opens X.toPresheafedSpace}
    (hφW : N.isOpenEmbedding.isOpenMap.functor.obj W' = W) (hW : W ≤ N)
    (hker : ∀ t, p.val.app (op W') t = 0 → ∃ t', a.val.app (op W') t' = t)
    (f : I → X.ringSheaf.obj.obj (op W))
    (hf : ∑ i, f i • M.val.map (homOfLE hW).op (restrictGenerator N M p i) = 0) :
    ∃ c : I' → X.ringSheaf.obj.obj (op W),
      ∀ i, f i = ∑ j, c j * X.ringSheaf.obj.map (homOfLE hW).op (restrictRelation N a j i) := by
  classical
  have r₁ : W ≤ N.isOpenEmbedding.isOpenMap.functor.obj W' := hφW.ge
  have r₂ : N.isOpenEmbedding.isOpenMap.functor.obj W' ≤ W := hφW.le
  let t := SheafOfModules.freeEvalSymm (R := (X.restrict N.isOpenEmbedding).ringSheaf)
    (op W') (fun i ↦ X.ringSheaf.obj.map (homOfLE r₂).op (f i))
  have ht : ∀ i, SheafOfModules.freeEval (op W') t i =
      X.ringSheaf.obj.map (homOfLE r₂).op (f i) := fun i ↦ by
    rw [SheafOfModules.freeEval_freeEvalSymm]
  have hpt : p.val.app (op W') t = 0 := val_app_freeEvalSymm_eq_zero p hφW hW f hf
  obtain ⟨t', ht'⟩ := hker t hpt
  refine ⟨fun j ↦ X.ringSheaf.obj.map (homOfLE r₁).op (SheafOfModules.freeEval (op W') t' j),
    fun i ↦ ?_⟩
  have h2 := freeEval_val_app_free a W' t' i
  rw [ht', ht] at h2
  have h3 := congrArg (X.ringSheaf.obj.map (homOfLE r₁).op) h2
  rw [ringSheaf_map_map, ringSheaf_map_self] at h3
  rw [h3]
  erw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  erw [map_mul]
  refine congrArg _ ?_
  exact (ringSheaf_map_map _ _ _).trans (ringSheaf_map_map hW _ _).symm

/-- **Theorem B for sheaves with a finite free resolution, on `X`.** Let `M` be a sheaf of
modules on `X` whose restriction to the open `N` has a finite free resolution. Then there are
sections `g : I → M(N)` and a matrix `A : I' → I → 𝒪(N)` of relations `∑ᵢ A j i • g i = 0`, with
`I`, `I'` finite, such that on every open `W ≤ N` on which `𝒪_X` is acyclic:
- `M` is acyclic on `W`;
- every section of `M` over `W` is a combination `∑ᵢ fᵢ • gᵢ|_W`;
- the relations between the `gᵢ|_W` are generated by the rows of `A`. -/
theorem exists_generators_acyclic (N : Opens X.toPresheafedSpace)
    (M : SheafOfModules.{u} X.ringSheaf) {d : ℕ}
    (h : ((X.restrictModules N).obj M).HasFreeResolutionLE d) :
    ∃ (I I' : Type u) (_ : Fintype I) (_ : Fintype I') (g : I → M.val.obj (op N))
      (A : I' → I → X.ringSheaf.obj.obj (op N)), (∀ j, ∑ i, A j i • g i = 0) ∧
      ∀ (W : Opens X.toPresheafedSpace) (hW : W ≤ N),
        (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
          ((TopCat.Sheaf.restrictOpen W).obj X.structureSheafAb) q)) →
        (∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
          ((TopCat.Sheaf.restrictOpen W).obj M.toAb) q)) ∧
        (∀ s : M.val.obj (op W), ∃ f : I → X.ringSheaf.obj.obj (op W),
          s = ∑ i, f i • M.val.map (homOfLE hW).op (g i)) ∧
        (∀ f : I → X.ringSheaf.obj.obj (op W),
          ∑ i, f i • M.val.map (homOfLE hW).op (g i) = 0 →
          ∃ c : I' → X.ringSheaf.obj.obj (op W),
            ∀ i, f i = ∑ j, c j * X.ringSheaf.obj.map (homOfLE hW).op (A j i)) := by
  classical
  obtain ⟨I, I', _, _, p, a, hap, H⟩ :=
    (h.of_iso (restrictModulesObjIso X N M)).exists_presentation_acyclic
  have := Fintype.ofFinite I
  have := Fintype.ofFinite I'
  have hN : N ≤ N.isOpenEmbedding.isOpenMap.functor.obj ⊤ := (TopCat.Sheaf.functor_obj_top N).ge
  refine ⟨I, I', inferInstance, inferInstance, restrictGenerator N M p, restrictRelation N a,
    sum_restrictRelation_smul p a hap, fun W hW hWa ↦ ?_⟩
  obtain ⟨W', hφW⟩ : ∃ W' : Opens (X.restrict N.isOpenEmbedding).toPresheafedSpace,
      N.isOpenEmbedding.isOpenMap.functor.obj W' = W :=
    ⟨preimageOpen N W, functor_obj_preimageOpen hW⟩
  have r₁ : W ≤ N.isOpenEmbedding.isOpenMap.functor.obj W' := hφW.ge
  have r₂ : N.isOpenEmbedding.isOpenMap.functor.obj W' ≤ W := hφW.le
  have hW'a : ∀ q, 0 < q → Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen W').obj (X.restrict N.isOpenEmbedding).structureSheafAb) q) :=
    fun q hq ↦ @Equiv.subsingleton _ _
      (structureSheafAbAddEquivOfEq (X.ofRestrict N.isOpenEmbedding) N.isOpenEmbedding W' hφW
        q).symm.toEquiv (hWa q hq)
  obtain ⟨hMa, hsurj, hker⟩ := H W' hW'a
  refine ⟨fun q hq ↦ ?_, fun s ↦ ?_, fun f hf ↦ ?_⟩
  · exact subsingleton_H_restrictOpen_of_restrict hφW (hMa q hq)
  · let s' : M.val.obj (op (N.isOpenEmbedding.isOpenMap.functor.obj W')) :=
      M.val.map (homOfLE r₂).op s
    obtain ⟨t, ht⟩ := hsurj ((restrictSectionsEquiv N M W').symm s')
    refine ⟨fun i ↦ X.ringSheaf.obj.map (homOfLE r₁).op (SheafOfModules.freeEval (op W') t i),
      ?_⟩
    have e1 : M.val.map (homOfLE r₁).op s' = s := by
      rw [sheafOfModules_map_map, sheafOfModules_map_self]
    rw [← e1, ← (restrictSectionsEquiv N M W').apply_symm_apply s', ← ht]
    exact map_val_app_free_eq_sum p hφW hW t
  · exact exists_eq_sum_restrictRelation p a hφW hW hker f hf

end AlgebraicGeometry.LocallyRingedSpace

end
