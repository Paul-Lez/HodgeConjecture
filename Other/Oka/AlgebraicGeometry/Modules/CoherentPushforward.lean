/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentModule
public import Other.Oka.AlgebraicGeometry.Modules.QuasicoherentSections
public import Other.Oka.AlgebraicGeometry.Modules.QuasicoherentCover
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Pushforward of coherent sheaves along closed immersions

Let `i : Z ⟶ P` be a closed immersion of schemes with `P` locally noetherian, and `F` a coherent
sheaf of `𝒪_Z`-modules. Then `i_* F` is a coherent sheaf of `𝒪_P`-modules
(`AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`).

The proof verifies the concrete criterion
`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_hasLocalModuleRelations`. On an affine open
`W ⊆ P` with ring `A = Γ(P, W)`, the preimage `U = i⁻¹(W)` is affine, `ρ : A → B = Γ(Z, U)` is
surjective, and `N = Γ(U, F)` is a finite `B`-module; for `h ∈ A` the preimage of `D(h)` is
`D(ρ h)`, and sections of `F` over `D(ρ h)` are fractions of sections over `U` since `F` is
quasi-coherent.
* Generators: finitely many generators of `N` generate `i_* F` near every point of `W`.
* Relations: the relations `a ∈ Aᵐ` with `∑ ρ(aⱼ) fⱼ = 0` form a finitely generated submodule
  of `Aᵐ` (`A` is noetherian), and its generators generate the relations locally.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry

open LocallyRingedSpace Scheme.Modules

namespace IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (F : X.Modules) [F.IsQuasicoherent]

include hU in
/-- `IsAffineOpen.exists_restrictOpen_eq_pow_smul` for an open `D` equal to `D(f)`. -/
lemma exists_restrictOpen_eq_pow_smul_of_eq (f : Γ(X, U)) {D : X.Opens}
    (hD : D = X.basicOpen f) (s : Γ(F, D)) :
    ∃ (k : ℕ) (t : Γ(F, U)), TopCat.Presheaf.restrictOpen t D (hD.le.trans (X.basicOpen_le f)) =
      TopCat.Presheaf.restrictOpen f D (hD.le.trans (X.basicOpen_le f)) ^ k • s := by
  subst hD
  exact hU.exists_restrictOpen_eq_pow_smul F f s

include hU in
/-- `IsAffineOpen.exists_pow_smul_eq_zero` for an open `D` equal to `D(f)`. -/
lemma exists_pow_smul_eq_zero_of_eq (f : Γ(X, U)) {D : X.Opens} (hD : D = X.basicOpen f)
    (t : Γ(F, U)) (ht : TopCat.Presheaf.restrictOpen t D (hD.le.trans (X.basicOpen_le f)) = 0) :
    ∃ k : ℕ, f ^ k • t = 0 := by
  subst hD
  exact hU.exists_pow_smul_eq_zero F f t ht

end IsAffineOpen

namespace Scheme.Hom

variable {Z P : Scheme.{u}} (i : Z ⟶ P)

/-- The ring maps `i.app` commute with restriction. -/
lemma app_restrictOpen {V W : P.Opens} (h : W ≤ V) (x : Γ(P, V)) :
    i.app W (TopCat.Presheaf.restrictOpen x W h) =
      TopCat.Presheaf.restrictOpen (i.app V x) (i ⁻¹ᵁ W) (i.preimage_mono h) := by
  change (P.presheaf.map (homOfLE h).op ≫ i.app W) x = _
  rw [i.naturality]
  rfl

end Scheme.Hom

variable {Z P : Scheme.{u}} (i : Z ⟶ P) (F : SheafOfModules.{u} Z.toLocallyRingedSpace.ringSheaf)

/-- Local generation of `i_* F` over an affine open `W₀` of `P` whose preimage carries finitely
many generators of the sections of `F`. -/
theorem pushforward_exists_generators [IsClosedImmersion i]
    (hq : SheafOfModules.IsQuasicoherent (R := Z.ringCatSheaf) F) (W₀ : P.Opens)
    (hW₀ : IsAffineOpen W₀)
    [Module.Finite Γ(Z, i ⁻¹ᵁ W₀) Γ((F : Z.Modules), i ⁻¹ᵁ W₀)] :
    ∃ (k : ℕ) (s : Fin k →
        ((SheafOfModules.pushforward.{u} i.toLRSHom.toRingSheafHom).obj F).val.obj (op W₀)),
      ∀ (W' : Opens P.toLocallyRingedSpace) (hW' : W' ≤ W₀)
        (t : ((SheafOfModules.pushforward.{u} i.toLRSHom.toRingSheafHom).obj F).val.obj
          (op W')), ∀ y ∈ W',
        ∃ (W'' : Opens P.toLocallyRingedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
          ∃ c : Fin k → P.toLocallyRingedSpace.presheaf.obj (op W''),
            sectRes _ hW'' t = ∑ l, c l • sectRes _ (hW''.trans hW') (s l) := by
  set F' : Z.Modules := F
  haveI : F'.IsQuasicoherent := hq
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := Γ(Z, i ⁻¹ᵁ W₀)) (M := Γ(F', i ⁻¹ᵁ W₀))
  refine ⟨k, s, fun W' hW' t y hy ↦ ?_⟩
  obtain ⟨h, hhW', hyh⟩ := hW₀.exists_basicOpen_le (V := W') ⟨y, hy⟩ (hW' hy)
  have hle : P.basicOpen h ≤ W₀ := P.basicOpen_le h
  have hD : i ⁻¹ᵁ P.basicOpen h = Z.basicOpen (i.app W₀ h) := Scheme.preimage_basicOpen i h
  set T : Γ(F', i ⁻¹ᵁ P.basicOpen h) :=
    TopCat.Presheaf.restrictOpen (show Γ(F', i ⁻¹ᵁ W') from t) _ (i.preimage_mono hhW')
  obtain ⟨r, t', ht'⟩ := (hW₀.preimage i).exists_restrictOpen_eq_pow_smul_of_eq F'
    (i.app W₀ h) hD T
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hs.symm ▸ Submodule.mem_top : t' ∈ Submodule.span Γ(Z, i ⁻¹ᵁ W₀) (Set.range s))
  choose a ha using fun l ↦ i.app_surjective W₀ hW₀ (b l)
  have hu : IsUnit (TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle : Γ(P, P.basicOpen h)) :=
    P.toRingedSpace.isUnit_res_basicOpen h
  set u : Γ(P, P.basicOpen h) := ↑(hu.unit⁻¹)
  have hu1 : u * TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle = 1 := hu.val_inv_mul
  refine ⟨P.basicOpen h, hhW', hyh,
    fun l ↦ u ^ r * TopCat.Presheaf.restrictOpen (a l) (P.basicOpen h) hle, ?_⟩
  set S : Fin k → Γ(F', i ⁻¹ᵁ P.basicOpen h) := fun l ↦
    TopCat.Presheaf.restrictOpen (s l) _ (i.preimage_mono hle)
  have hH : i.app (P.basicOpen h) (TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle) =
      TopCat.Presheaf.restrictOpen (i.app W₀ h) (i ⁻¹ᵁ P.basicOpen h) (i.preimage_mono hle) :=
    i.app_restrictOpen hle h
  have key : ∑ l, i.app (P.basicOpen h) (TopCat.Presheaf.restrictOpen (a l) (P.basicOpen h) hle)
      • S l = i.app (P.basicOpen h) (TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle) ^ r • T
      := by
    rw [hH, ← ht', ← hb]
    rw [show TopCat.Presheaf.restrictOpen (∑ l, b l • s l) (i ⁻¹ᵁ P.basicOpen h)
        (hD.le.trans (Z.basicOpen_le _)) = ∑ l, TopCat.Presheaf.restrictOpen (b l • s l)
          (i ⁻¹ᵁ P.basicOpen h) (i.preimage_mono hle) from
      map_sum (F'.presheaf.map (homOfLE _).op).hom _ _]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [mres_smul, ← ha l, ← i.app_restrictOpen hle]
  change T = ∑ l, i.app (P.basicOpen h)
    (u ^ r * TopCat.Presheaf.restrictOpen (a l) (P.basicOpen h) hle) • S l
  simp only [map_mul, map_pow, mul_smul]
  rw [← Finset.smul_sum, key, smul_smul, ← mul_pow, ← map_mul, hu1, map_one, one_pow, one_smul]

/-- **The relations between sections of `i_* F` are locally finitely generated**, for a closed
immersion `i : Z ⟶ P` into a locally noetherian scheme and a quasi-coherent `F`. -/
theorem hasLocalModuleRelations_pushforward [IsClosedImmersion i] [IsLocallyNoetherian P]
    (hq : SheafOfModules.IsQuasicoherent (R := Z.ringCatSheaf) F) :
    HasLocalModuleRelations ((SheafOfModules.pushforward.{u} i.toLRSHom.toRingSheafHom).obj F) := by
  set F' : Z.Modules := F
  haveI : F'.IsQuasicoherent := hq
  intro V m f x hx
  obtain ⟨W, hWaff, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.1 P.isBasis_affineOpens (U := V) hx
  haveI : IsNoetherianRing Γ(P, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWaff⟩
  set f' : Fin m → Γ(F', i ⁻¹ᵁ W) := fun j ↦
    TopCat.Presheaf.restrictOpen (show Γ(F', i ⁻¹ᵁ V) from f j) _ (i.preimage_mono hWV)
  let Rel : Submodule Γ(P, W) (Fin m → Γ(P, W)) :=
    { carrier := {a | ∑ j, i.app W (a j) • f' j = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Pi.add_apply, map_add, add_smul,
          Finset.sum_add_distrib] at ha hb ⊢
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at ha ⊢
        rw [← Finset.smul_sum, ha, smul_zero] }
  obtain ⟨k, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian Rel)
  have hgRel : ∀ l, g l ∈ Rel := fun l ↦ hg ▸ Submodule.subset_span ⟨l, rfl⟩
  refine ⟨W, hWV, k, g, hxW, fun l ↦ hgRel l, ?_⟩
  intro W' hW' a ha y hy
  obtain ⟨h, hhW', hyh⟩ := hWaff.exists_basicOpen_le (V := W') ⟨y, hy⟩ (hW' hy)
  have hle : P.basicOpen h ≤ W := P.basicOpen_le h
  have hD : i ⁻¹ᵁ P.basicOpen h = Z.basicOpen (i.app W h) := Scheme.preimage_basicOpen i h
  haveI := hWaff.isLocalization_basicOpen h
  obtain ⟨⟨_, r, rfl⟩, hr⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers h)
    (fun j ↦ (TopCat.Presheaf.restrictOpen (a j) (P.basicOpen h) hhW' : Γ(P, P.basicOpen h)))
  choose a' ha' using hr
  have ha'' : ∀ j, TopCat.Presheaf.restrictOpen (a' j) (P.basicOpen h) hle =
      TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle ^ r *
        TopCat.Presheaf.restrictOpen (a j) (P.basicOpen h) hhW' := by
    intro j
    refine (ha' j).trans ?_
    rw [Algebra.smul_def, map_pow]
    rfl
  set E : Γ(F', i ⁻¹ᵁ W) := ∑ j, i.app W (a' j) • f' j
  have ha0 : ∑ j, i.app W' (a j) • TopCat.Presheaf.restrictOpen (show Γ(F', i ⁻¹ᵁ V) from f j)
      (i ⁻¹ᵁ W') (i.preimage_mono (hW'.trans hWV)) = 0 := ha
  have hE : TopCat.Presheaf.restrictOpen E (i ⁻¹ᵁ P.basicOpen h)
      (hD.le.trans (Z.basicOpen_le _)) = 0 := by
    have h0 := congrArg (fun e ↦ TopCat.Presheaf.restrictOpen e (i ⁻¹ᵁ P.basicOpen h)
      (i.preimage_mono hhW')) ha0
    simp only [mres_zero] at h0
    rw [← smul_zero (i.app (P.basicOpen h)
      (TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle) ^ r), ← h0]
    rw [show TopCat.Presheaf.restrictOpen E (i ⁻¹ᵁ P.basicOpen h)
        (hD.le.trans (Z.basicOpen_le _)) = ∑ j, TopCat.Presheaf.restrictOpen
          (i.app W (a' j) • f' j) (i ⁻¹ᵁ P.basicOpen h) (i.preimage_mono hle) from
      map_sum (F'.presheaf.map (homOfLE _).op).hom _ _]
    rw [show TopCat.Presheaf.restrictOpen (∑ j, i.app W' (a j) •
        TopCat.Presheaf.restrictOpen (show Γ(F', i ⁻¹ᵁ V) from f j)
          (i ⁻¹ᵁ W') (i.preimage_mono (hW'.trans hWV))) (i ⁻¹ᵁ P.basicOpen h)
          (i.preimage_mono hhW') = ∑ j, TopCat.Presheaf.restrictOpen (i.app W' (a j) •
        TopCat.Presheaf.restrictOpen (show Γ(F', i ⁻¹ᵁ V) from f j)
          (i ⁻¹ᵁ W') (i.preimage_mono (hW'.trans hWV))) (i ⁻¹ᵁ P.basicOpen h)
          (i.preimage_mono hhW') from
      map_sum (F'.presheaf.map (homOfLE _).op).hom _ _]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mres_smul, mres_smul, ← i.app_restrictOpen, ← i.app_restrictOpen, ha'', map_mul,
      map_pow, mul_smul, mres_res, mres_res]
    exact hle
  obtain ⟨N, hN⟩ := (hWaff.preimage i).exists_pow_smul_eq_zero_of_eq F' (i.app W h) hD E hE
  have hmem : h ^ N • a' ∈ Rel := by
    change ∑ j, i.app W ((h ^ N • a') j) • f' j = 0
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, mul_smul]
    rw [← Finset.smul_sum]
    exact hN
  rw [← hg] at hmem
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(P, W)).1 hmem
  have hu : IsUnit (TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle : Γ(P, P.basicOpen h)) :=
    P.toRingedSpace.isUnit_res_basicOpen h
  set u : Γ(P, P.basicOpen h) := ↑(hu.unit⁻¹)
  have hu1 : u * TopCat.Presheaf.restrictOpen h (P.basicOpen h) hle = 1 := hu.val_inv_mul
  refine ⟨P.basicOpen h, hhW', hyh,
    fun l ↦ u ^ (r + N) * TopCat.Presheaf.restrictOpen (β l) (P.basicOpen h) hle, fun j ↦ ?_⟩
  have hβj : ∑ l, β l * g l j = h ^ N * a' j := by
    have := congrFun hβ j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  change TopCat.Presheaf.restrictOpen (a j) (P.basicOpen h) hhW' = ∑ l,
    u ^ (r + N) * TopCat.Presheaf.restrictOpen (β l) (P.basicOpen h) hle *
      TopCat.Presheaf.restrictOpen (g l j) (P.basicOpen h) (hhW'.trans hW')
  simp only [mul_assoc, ← Finset.mul_sum, ← ores_mul]
  rw [show ∑ l, TopCat.Presheaf.restrictOpen (β l * g l j) (P.basicOpen h) (hhW'.trans hW') =
      TopCat.Presheaf.restrictOpen (∑ l, β l * g l j) (P.basicOpen h) hle from
    (map_sum (P.presheaf.map (homOfLE _).op).hom _ _).symm, hβj, ores_mul, ores_pow, ha'',
    show ∀ U H A : Γ(P, P.basicOpen h), U ^ (r + N) * (H ^ N * (H ^ r * A)) =
      (U * H) ^ (r + N) * A from fun U H A ↦ by ring, hu1, one_pow, one_mul]

/-- **`i_* F` is locally finitely generated** for a closed immersion `i` and a quasi-coherent
`F` of finite type. -/
theorem isLocallyFinitelyGeneratedModule_pushforward [IsClosedImmersion i]
    (hq : SheafOfModules.IsQuasicoherent (R := Z.ringCatSheaf) F)
    (hfin : SheafOfModules.IsFiniteType (R := Z.ringCatSheaf) F) :
    IsLocallyFinitelyGeneratedModule
      ((SheafOfModules.pushforward.{u} i.toLRSHom.toRingSheafHom).obj F) := by
  set F' : Z.Modules := F
  haveI : F'.IsQuasicoherent := hq
  haveI : F'.IsFiniteType := hfin
  intro x
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨W, hWaff, hxW, -⟩ :=
      Opens.isBasis_iff_nbhd.1 P.isBasis_affineOpens (U := ⊤) (Set.mem_univ (i.base z))
    obtain ⟨g, hzg, hgfin⟩ := (hWaff.preimage i).exists_module_finite_basicOpen F' z hxW
    obtain ⟨h, rfl⟩ := i.app_surjective W hWaff g
    have hD : i ⁻¹ᵁ P.basicOpen h = Z.basicOpen (i.app W h) := Scheme.preimage_basicOpen i h
    rw [← hD] at hgfin hzg
    obtain ⟨k, s, hs⟩ := pushforward_exists_generators i F hq (P.basicOpen h) (hWaff.basicOpen h)
    exact ⟨P.basicOpen h, k, s, hzg, hs⟩
  · have hcl : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
    obtain ⟨W, hWaff, hxW, hWc⟩ := Opens.isBasis_iff_nbhd.1 P.isBasis_affineOpens
      (U := ⟨(Set.range i.base)ᶜ, hcl.isOpen_compl⟩) hx
    have hbot : i ⁻¹ᵁ W = ⊥ := le_bot_iff.mp fun z hz ↦ hWc hz ⟨z, rfl⟩
    haveI : Subsingleton Γ(Z, i ⁻¹ᵁ W) := by rw [hbot]; infer_instance
    haveI : Subsingleton Γ(F', i ⁻¹ᵁ W) := Module.subsingleton Γ(Z, i ⁻¹ᵁ W) _
    haveI : Module.Finite Γ(Z, i ⁻¹ᵁ W) Γ(F', i ⁻¹ᵁ W) := Module.Finite.of_finite
    obtain ⟨k, s, hs⟩ := pushforward_exists_generators i F hq W hWaff
    exact ⟨W, k, s, hxW, hs⟩

/-- **The pushforward of a coherent sheaf along a closed immersion into a locally noetherian
scheme is coherent.** -/
theorem isCoherent_pushforward_of_isClosedImmersion [IsClosedImmersion i]
    [IsLocallyNoetherian P] [hF : F.IsCoherent] :
    ((SheafOfModules.pushforward.{u} i.toLRSHom.toRingSheafHom).obj F).IsCoherent :=
  isCoherent_of_hasLocalModuleRelations _
    (isLocallyFinitelyGeneratedModule_pushforward i F
      (Scheme.Modules.isQuasicoherent_of_isCoherent F) hF.isFiniteType)
    (hasLocalModuleRelations_pushforward i F (Scheme.Modules.isQuasicoherent_of_isCoherent F))

end AlgebraicGeometry

end
