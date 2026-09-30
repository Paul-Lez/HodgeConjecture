/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.LocalRing.Module
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Criterion
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalk
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.RestrictModulesOver
public import Other.Oka.Geometry.RingedSpace.OpenImmersion

/-! # Local freeness from projective stalks -/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite Limits

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}


lemma flat_stalkMap_of_isIso {X : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [∀ x, IsIso (f.stalkMap x)] (x : X) : ((f.stalkMap x).hom).Flat :=
  (faithfullyFlat_stalkMap_of_isIso f x).flat

section Restrict

variable (U : Opens Y) (V : Opens (Y.restrict U.isOpenEmbedding))


def restrictRestrictIso :
    Y.restrict (imOpen U V).isOpenEmbedding ≅
      (Y.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq (Y.ofRestrict (imOpen U V).isOpenEmbedding)
    ((Y.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
      Y.ofRestrict U.isOpenEmbedding)
    (by rw [range_ofRestrict, range_ofRestrict_comp])


lemma restrictRestrictIso_hom_fac :
    (restrictRestrictIso U V).hom ≫
        (Y.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding ≫
          Y.ofRestrict U.isOpenEmbedding =
      Y.ofRestrict (imOpen U V).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _


def restrictModulesRestrictIso (M : SheafOfModules.{u} Y.ringSheaf) :
    (Y.restrictModules (imOpen U V)).obj M ≅
      (restrictRestrictIso U V).hom.pullbackModules.obj
        (((Y.restrict U.isOpenEmbedding).restrictModules V).obj
          ((Y.restrictModules U).obj M)) :=
  Hom.pullbackModulesObjCompIso _ _ _ (restrictRestrictIso_hom_fac U V) M ≪≫
    (restrictRestrictIso U V).hom.pullbackModules.mapIso
      (Hom.pullbackModulesObjCompIso _ _ _ rfl M)


lemma hasFreeResolutionLE_restrictModules_of_restrict {M : SheafOfModules.{u} Y.ringSheaf}
    {n : ℕ} (h : (((Y.restrict U.isOpenEmbedding).restrictModules V).obj
      ((Y.restrictModules U).obj M)).HasFreeResolutionLE n) :
    ((Y.restrictModules (imOpen U V)).obj M).HasFreeResolutionLE n :=
  ((restrictRestrictIso U V).hom.hasFreeResolutionLE_pullbackModules
    (fun x ↦ (faithfullyFlat_stalkMap_iso_hom _ x).flat) h).of_iso
    (restrictModulesRestrictIso U V M).symm


lemma isZero_restrictModules_of_restrict {M : SheafOfModules.{u} Y.ringSheaf}
    (h : IsZero (((Y.restrict U.isOpenEmbedding).restrictModules V).obj
      ((Y.restrictModules U).obj M))) :
    IsZero ((Y.restrictModules (imOpen U V)).obj M) :=
  ((restrictRestrictIso U V).hom.isZero_pullbackModules_obj h).of_iso
    (restrictModulesRestrictIso U V M)


lemma mem_imOpen {y : Y} (hy : y ∈ U) (h : (⟨y, hy⟩ : Y.restrict U.isOpenEmbedding) ∈ V) :
    y ∈ imOpen U V :=
  ⟨⟨y, hy⟩, h, rfl⟩

end Restrict

section LE

variable {V W : Opens Y}


instance (h : V ≤ W) (x : Y.restrict V.isOpenEmbedding) : IsIso ((Y.restrictLE h).stalkMap x) :=
  isIso_stalkMap_liftRestrict _ _ _ x


def restrictModulesLEIso (h : V ≤ W) (M : SheafOfModules.{u} Y.ringSheaf) :
    (Y.restrictModules V).obj M ≅
      (Y.restrictLE h).pullbackModules.obj ((Y.restrictModules W).obj M) :=
  Hom.pullbackModulesObjCompIso _ _ _ (restrictLE_fac Y h) M


lemma hasFreeResolutionLE_restrictModules_of_le (h : V ≤ W) {M : SheafOfModules.{u} Y.ringSheaf}
    {n : ℕ} (hM : ((Y.restrictModules W).obj M).HasFreeResolutionLE n) :
    ((Y.restrictModules V).obj M).HasFreeResolutionLE n :=
  ((Y.restrictLE h).hasFreeResolutionLE_pullbackModules (flat_stalkMap_of_isIso _) hM).of_iso
    (restrictModulesLEIso h M).symm


lemma isZero_restrictModules_of_le (h : V ≤ W) {M : SheafOfModules.{u} Y.ringSheaf}
    (hM : IsZero ((Y.restrictModules W).obj M)) : IsZero ((Y.restrictModules V).obj M) :=
  ((Y.restrictLE h).isZero_pullbackModules_obj hM).of_iso (restrictModulesLEIso h M)

end LE


lemma isCoherent_restrictModules (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent]
    (U : Opens Y) : ((Y.restrictModules U).obj M).IsCoherent :=
  (isCoherent_over_iff_isCoherent_restrictModules Y U M).1 (SheafOfModules.IsCoherent.over M U)


theorem exists_epi_free_restrictModules (M : SheafOfModules.{u} Y.ringSheaf) [M.IsFiniteType]
    (y : Y) : ∃ (U : Opens Y) (_ : y ∈ U) (I : Type u) (_ : Finite I)
      (π : SheafOfModules.free I ⟶ (Y.restrictModules U).obj M), Epi π := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u} M
  have hcov : IsOpenCover σ.X := (Opens.coversTop_iff _ σ.X).1 σ.coversTop
  obtain ⟨i, hi⟩ : ∃ i, y ∈ σ.X i := by
    have : y ∈ (⊤ : Opens Y.toPresheafedSpace) := trivial
    rw [← hcov.iSup_eq_top] at this
    exact Opens.mem_iSup.1 this
  let G := σ.generators i
  haveI : G.IsFiniteType := hσ.isFiniteType i
  let E := restrictOverEquiv Y (σ.X i)
  let e₁ : SheafOfModules.free G.I ≅ E.functor.obj (SheafOfModules.free G.I) :=
    ((Y.ofRestrict (σ.X i).isOpenEmbedding).pullbackModulesFreeIso G.I).symm ≪≫
      restrictModulesObjIso Y (σ.X i) (SheafOfModules.free G.I) ≪≫
        E.functor.mapIso (SheafOfModules.overFreeIso G.I (σ.X i)).symm
  refine ⟨σ.X i, hi, G.I, inferInstance,
    e₁.hom ≫ E.functor.map G.π ≫ (restrictModulesObjIso Y (σ.X i) M).inv, ?_⟩
  haveI : E.functor.IsLeftAdjoint := E.toAdjunction.isLeftAdjoint
  haveI : E.functor.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_isLeftAdjoint _
  haveI h1 : Epi (E.functor.map G.π) := E.functor.map_epi _
  haveI h2 : Epi (restrictModulesObjIso Y (σ.X i) M).inv := inferInstance
  haveI h3 : Epi e₁.hom := inferInstance
  exact @epi_comp _ _ _ _ _ _ h3 _ (@epi_comp _ _ _ _ _ _ h1 _ h2)


theorem exists_isZero_restrictModules (M : SheafOfModules.{u} Y.ringSheaf) [M.IsFiniteType]
    (y : Y) (hy : Subsingleton ((Y.stalkFunctor y).obj M)) :
    ∃ (U : Opens Y) (_ : y ∈ U), IsZero ((Y.restrictModules U).obj M) := by
  obtain ⟨U, hyU, I, _, π, _⟩ := exists_epi_free_restrictModules M y
  let y' : Y.restrict U.isOpenEmbedding := ⟨y, hyU⟩
  haveI : Subsingleton (((Y.restrict U.isOpenEmbedding).stalkFunctor y').obj
      ((Y.restrictModules U).obj M)) :=
    @Hom.subsingleton_stalk_pullbackModules _ _ (Y.ofRestrict U.isOpenEmbedding) y' _ M hy
  obtain ⟨V, hyV, hV⟩ := exists_forall_subsingleton_stalk π y'
  refine ⟨imOpen U V, mem_imOpen U V hyU hyV, isZero_restrictModules_of_restrict U V ?_⟩
  refine isZero_of_forall_subsingleton_stalk _ fun w ↦ ?_
  exact @Hom.subsingleton_stalk_pullbackModules _ _
    ((Y.restrict U.isOpenEmbedding).ofRestrict V.isOpenEmbedding) w _ _ (hV _ w.2)


lemma hasFreeResolutionLE_zero_of_isZero {M : SheafOfModules.{u} Y.ringSheaf} {κ : Type u}
    [Finite κ] (φ : SheafOfModules.free κ ⟶ M) (W : Opens Y)
    (hZK : IsZero ((Y.restrictModules W).obj (kernel φ)))
    (hZQ : IsZero ((Y.restrictModules W).obj (cokernel φ))) :
    ((Y.restrictModules W).obj M).HasFreeResolutionLE 0 := by
  haveI : PreservesFiniteLimits (Y.restrictModules W) :=
    (Y.ofRestrict W.isOpenEmbedding).preservesFiniteLimits_pullbackModules
      (flat_stalkMap_of_isIso _)
  haveI : PreservesColimits (Y.restrictModules W) :=
    (Y.ofRestrict W.isOpenEmbedding).pullbackModulesAdj.leftAdjoint_preservesColimits
  haveI : Mono ((Y.restrictModules W).map φ) :=
    Preadditive.mono_of_isZero_kernel _
      (hZK.of_iso (PreservesKernel.iso (Y.restrictModules W) φ).symm)
  haveI : Epi ((Y.restrictModules W).map φ) :=
    Preadditive.epi_of_isZero_cokernel _
      (hZQ.of_iso (PreservesCokernel.iso (Y.restrictModules W) φ).symm)
  haveI : IsIso ((Y.restrictModules W).map φ) := isIso_of_mono_of_epi _
  exact .free 0 κ ((asIso ((Y.restrictModules W).map φ)).symm ≪≫
    (Y.ofRestrict W.isOpenEmbedding).pullbackModulesFreeIso κ)


theorem exists_hasFreeResolutionLE_zero (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent]
    (y : Y) (h : HasProjectiveDimensionLE ((Y.stalkFunctor y).obj M) 0) :
    ∃ (U : Opens Y) (_ : y ∈ U), ((Y.restrictModules U).obj M).HasFreeResolutionLE 0 := by
  classical
  obtain ⟨U, hyU, I, _, π, _⟩ := exists_epi_free_restrictModules M y
  let Y' := Y.restrict U.isOpenEmbedding
  let M' := (Y.restrictModules U).obj M
  let y' : Y' := ⟨y, hyU⟩
  haveI : M'.IsCoherent := isCoherent_restrictModules M U
  haveI hpd : HasProjectiveDimensionLE ((Y'.stalkFunctor y').obj M') 0 :=
    @Hom.hasProjectiveDimensionLE_stalk_pullbackModules _ _ (Y.ofRestrict U.isOpenEmbedding) y' _
      M 0 h
  let N := (Y'.stalkFunctor y').obj M'
  haveI : Module.Projective (Y'.presheaf.stalk y') N :=
    ModuleCat.projective_of_hasProjectiveDimensionLE_zero N
  have hspan := span_germ_eq_top π y'
  haveI : Module.Finite (Y'.presheaf.stalk y') N := by
    haveI := Fintype.ofFinite I
    refine
      ⟨⟨(Set.finite_range fun i ↦ germTop M' y' (generatorSection π i)).toFinset, ?_⟩⟩
    rw [Set.Finite.coe_toFinset]
    exact hspan
  haveI := Module.finitePresentation_of_projective (Y'.presheaf.stalk y') N
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat
    (fun i ↦ germTop M' y' (generatorSection π i)) hspan
  haveI : Finite κ := Module.Finite.finite_basis b
  let φ : SheafOfModules.free κ ⟶ M' :=
    M'.freeHomEquiv.symm (fun k ↦ M'.freeHomEquiv π (a k))
  have hφ : ∀ k, generatorSection φ k = generatorSection π (a k) := fun k ↦
    congrArg (fun s ↦ PresheafOfModules.sections.eval s (op ⊤))
      (congrFun (M'.freeHomEquiv.apply_symm_apply _) k)
  have hφb : ∀ k, (Y'.stalkFunctor y').map φ (basisStalkFree κ y' k) = b k := fun k ↦ by
    rw [basisStalkFree_apply, stalkFunctor_map_germTop, ← generatorSection_comp, Category.id_comp,
      hφ, hb]
  have hbij : Function.Bijective ((Y'.stalkFunctor y').map φ) := by
    have heq : ((Y'.stalkFunctor y').map φ).hom =
        ((basisStalkFree κ y').equiv b (Equiv.refl κ)).toLinearMap :=
      (basisStalkFree κ y').ext fun k ↦ by simp [hφb]
    have hfun : ⇑((Y'.stalkFunctor y').map φ) =
        ⇑((basisStalkFree κ y').equiv b (Equiv.refl κ)) :=
      funext fun x ↦ LinearMap.congr_fun heq x
    rw [hfun]
    exact LinearEquiv.bijective _
  -- the kernel vanishes near `y'`
  haveI hKft : (kernel φ).IsFiniteType := SheafOfModules.isFiniteType_kernel_of_isCoherent φ
  have hKsub : Subsingleton ((Y'.stalkFunctor y').obj (kernel φ)) := by
    refine ⟨fun m₁ m₂ ↦ injective_stalk_of_mono (kernel.ι φ) y' (hbij.1 ?_)⟩
    rw [stalkFunctor_map_map_eq_zero _ _ (kernel.condition φ),
      stalkFunctor_map_map_eq_zero _ _ (kernel.condition φ)]
  obtain ⟨W₁, hyW₁, hZ₁⟩ := exists_isZero_restrictModules (kernel φ) y' hKsub
  -- the cokernel vanishes near `y'`
  haveI hQft : (cokernel φ).IsFiniteType := SheafOfModules.isFiniteType_cokernel φ
  have hQsub : Subsingleton ((Y'.stalkFunctor y').obj (cokernel φ)) := by
    refine ⟨fun q₁ q₂ ↦ ?_⟩
    have hzero : ∀ q : (Y'.stalkFunctor y').obj (cokernel φ), q = 0 := fun q ↦ by
      obtain ⟨m, rfl⟩ := surjective_stalk_of_epi (cokernel.π φ) y' q
      obtain ⟨x, rfl⟩ := hbij.2 m
      exact stalkFunctor_map_map_eq_zero _ _ (cokernel.condition φ) y' x
    rw [hzero q₁, hzero q₂]
  obtain ⟨W₂, hyW₂, hZ₂⟩ := exists_isZero_restrictModules (cokernel φ) y' hQsub
  -- on `W₁ ⊓ W₂`, `φ` is an isomorphism
  have hres := hasFreeResolutionLE_zero_of_isZero φ (W₁ ⊓ W₂)
    (isZero_restrictModules_of_le inf_le_left hZ₁)
    (isZero_restrictModules_of_le inf_le_right hZ₂)
  exact ⟨imOpen U (W₁ ⊓ W₂), mem_imOpen U _ hyU ⟨hyW₁, hyW₂⟩,
    hasFreeResolutionLE_restrictModules_of_restrict U _ hres⟩


attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- A basis of a coherent module stalk spreads to a local trivialization with the same index
type. -/
theorem exists_restrictModules_iso_free_of_basis
    (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent]
    (y : Y) {I : Type u}
    (b : Module.Basis I (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj M)) :
    ∃ (U : Opens Y) (_ : y ∈ U),
      Nonempty ((Y.restrictModules U).obj M ≅ SheafOfModules.free I) := by
  classical
  let N := (Y.stalkFunctor y).obj M
  haveI : Projective N :=
    (IsProjective.iff_projective N).1 (Module.Projective.of_basis b)
  have hpd : HasProjectiveDimensionLE N 0 :=
    (projective_iff_hasProjectiveDimensionLE_zero N).mp inferInstance
  obtain ⟨U, hyU, hU⟩ := exists_hasFreeResolutionLE_zero M y hpd
  cases hU with
  | free _ κ e =>
      let Y' := Y.restrict U.isOpenEmbedding
      let M' := (Y.restrictModules U).obj M
      let y' : Y' := ⟨y, hyU⟩
      let f := Y.ofRestrict U.isOpenEmbedding
      let eR := f.stalkMapRingEquiv y'
      let ePull := f.stalkPullbackModulesSemilinearEquiv y' M
      have hrankPull :
          Module.rank (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj M) =
            Module.rank (Y'.presheaf.stalk y') ((Y'.stalkFunctor y').obj M') := by
        exact rank_eq_of_equiv_equiv eR ePull.toAddEquiv eR.bijective
          (fun r m ↦ ePull.map_smulₛₗ r m)
      let eStalk := (Y'.stalkFunctor y').mapIso e
      have hrankIso :
          Module.rank (Y'.presheaf.stalk y') ((Y'.stalkFunctor y').obj M') =
            Module.rank (Y'.presheaf.stalk y')
              ((Y'.stalkFunctor y').obj (SheafOfModules.free κ)) :=
        eStalk.toLinearEquiv.rank_eq
      have hcardI : Cardinal.mk I =
          Module.rank (Y.presheaf.stalk y) ((Y.stalkFunctor y).obj M) := by
        simpa only [Cardinal.lift_id] using b.mk_eq_rank
      have hcardκ : Cardinal.mk κ =
          Module.rank (Y'.presheaf.stalk y')
            ((Y'.stalkFunctor y').obj (SheafOfModules.free κ)) := by
        simpa only [Cardinal.lift_id] using (basisStalkFree κ y').mk_eq_rank
      obtain ⟨eκI⟩ := Cardinal.eq.mp
        (hcardκ.trans (hrankIso.symm.trans (hrankPull.symm.trans hcardI.symm)))
      exact ⟨U, hyU, ⟨e ≪≫
        (SheafOfModules.freeFunctor (R := Y'.ringSheaf)).mapIso eκI.toIso⟩⟩

end AlgebraicGeometry.LocallyRingedSpace
