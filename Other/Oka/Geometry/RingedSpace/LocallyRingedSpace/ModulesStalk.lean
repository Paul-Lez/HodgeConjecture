/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Other.Oka.Algebra.Category.ModuleCat.ProjectiveDimension
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Free
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.FreeResolution
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.LocallySurjective
public import Other.Oka.AnalyticSpace.PullbackModulesStalk
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.FaithfullyFlatStalkMap
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesComp

/-!
# Stalks of sheaves of modules on a locally ringed space

This file relates vanishing, finite free generators, projective dimension, and pullback to the
corresponding statements on module-valued stalks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory TopologicalSpace Opposite Limits ZeroObject

namespace AlgebraicGeometry.LocallyRingedSpace

section Algebra

variable {R S : Type u} [CommRing R] [CommRing S]

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Extension of scalars along a ring equivalence is semilinearly equivalent to the original
module. -/
def extendScalarsSemilinearEquiv (e : R ≃+* S) (N : ModuleCat.{u} R) :
    N ≃ₛₗ[RingHomClass.toRingHom e]
      (ModuleCat.extendScalars (RingHomClass.toRingHom e)).obj N := by
  let ψ : R →ₗ[R] (ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj (ModuleCat.of S S) :=
    { toFun := fun r ↦ (e r : S)
      map_add' := fun a b ↦ map_add e a b
      map_smul' := fun a b ↦ by
        change e (a * b) = e a * e b
        exact map_mul e a b }
  have hψ : Function.Bijective ψ := e.bijective
  let E : N ≃ₗ[R] TensorProduct R
      ((ModuleCat.restrictScalars (RingHomClass.toRingHom e)).obj (ModuleCat.of S S)) N :=
    (TensorProduct.lid R N).symm ≪≫ₗ (LinearEquiv.ofBijective ψ hψ).rTensor N
  refine { E.toAddEquiv with map_smul' := fun r n ↦ ?_ }
  change E (r • n) = _
  rw [map_smul]
  change r • ((ψ 1 : _) ⊗ₜ[R] n) = _
  rw [TensorProduct.smul_tmul']
  rfl

end Algebra

variable {X Y : LocallyRingedSpace.{u}}

/-- A sheaf of modules whose stalks all vanish is zero. -/
theorem isZero_of_forall_subsingleton_stalk (M : SheafOfModules.{u} Y.ringSheaf)
    (h : ∀ y : Y, Subsingleton ((Y.stalkFunctor y).obj M)) : IsZero M := by
  have : Mono (0 : M ⟶ 0) := by
    refine SheafOfModules.mono_of_forall_mono_stalkFunctor_map (hR := Y.isSheaf_ringSheaf) _
      fun y ↦ ?_
    haveI := h y
    exact (ModuleCat.mono_iff_injective _).2 fun a b _ ↦ @Subsingleton.elim _ (h y) a b
  exact IsZero.of_mono (0 : M ⟶ 0) (isZero_zero _)

/-- The ring equivalence induced by an isomorphism on a stalk. -/
abbrev Hom.stalkMapRingEquiv (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    Y.presheaf.stalk (f.base x) ≃+* X.presheaf.stalk x :=
  (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- A pullback stalk along a stalk isomorphism is semilinearly equivalent to the source stalk. -/
def Hom.stalkPullbackModulesSemilinearEquiv (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)]
    (M : SheafOfModules.{u} Y.ringSheaf) :
    (Y.stalkFunctor (f.base x)).obj M ≃ₛₗ[RingHomClass.toRingHom (f.stalkMapRingEquiv x)]
      (X.stalkFunctor x).obj (f.pullbackModules.obj M) :=
  (extendScalarsSemilinearEquiv (f.stalkMapRingEquiv x) _).trans
    ((f.pullbackModulesStalkIso x).app M).symm.toLinearEquiv

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Vanishing of stalks transfers along a stalk isomorphism. -/
lemma Hom.subsingleton_stalk_pullbackModules (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)]
    (M : SheafOfModules.{u} Y.ringSheaf) [Subsingleton ((Y.stalkFunctor (f.base x)).obj M)] :
    Subsingleton ((X.stalkFunctor x).obj (f.pullbackModules.obj M)) :=
  (f.stalkPullbackModulesSemilinearEquiv x M).toEquiv.symm.subsingleton

/-- Projective-dimension bounds transfer along a stalk isomorphism. -/
lemma Hom.hasProjectiveDimensionLE_stalk_pullbackModules (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] (M : SheafOfModules.{u} Y.ringSheaf) (k : ℕ)
    [HasProjectiveDimensionLE ((Y.stalkFunctor (f.base x)).obj M : ModuleCat _) k] :
    HasProjectiveDimensionLE ((X.stalkFunctor x).obj (f.pullbackModules.obj M)) k :=
  ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv (f.stalkMapRingEquiv x)
    (f.stalkPullbackModulesSemilinearEquiv x M) k

/-- Pullback along flat stalk maps preserves finite free resolutions. -/
theorem Hom.hasFreeResolutionLE_pullbackModules (f : X ⟶ Y)
    (hflat : ∀ x : X, ((f.stalkMap x).hom).Flat) {M : SheafOfModules.{u} Y.ringSheaf} {n : ℕ}
    (h : M.HasFreeResolutionLE n) : (f.pullbackModules.obj M).HasFreeResolutionLE n := by
  haveI := f.preservesFiniteLimits_pullbackModules hflat
  haveI : f.pullbackModules.IsLeftAdjoint := f.pullbackModulesAdj.isLeftAdjoint
  haveI : PreservesColimits f.pullbackModules := f.pullbackModulesAdj.leftAdjoint_preservesColimits
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint f.pullbackModules
  exact h.map _ fun I _ ↦ f.pullbackModulesFreeIso I

/-- Pullback preserves zero objects. -/
lemma Hom.isZero_pullbackModules_obj (f : X ⟶ Y) {M : SheafOfModules.{u} Y.ringSheaf}
    (h : IsZero M) : IsZero (f.pullbackModules.obj M) := by
  haveI : f.pullbackModules.IsLeftAdjoint := f.pullbackModulesAdj.isLeftAdjoint
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint f.pullbackModules
  exact f.pullbackModules.map_isZero h

/-- Objectwise comparison for pullback along a composite. -/
def Hom.pullbackModulesObjCompIso {Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (M : SheafOfModules.{u} Z.ringSheaf) :
    h.pullbackModules.obj M ≅ f.pullbackModules.obj (g.pullbackModules.obj M) :=
  (Hom.pullbackModulesCongr e.symm).app M ≪≫ ((Hom.pullbackModulesComp f g).app M).symm

/-- The global section obtained from the image of a free generator. -/
abbrev generatorSection {M : SheafOfModules.{u} Y.ringSheaf} {I : Type u}
    (π : SheafOfModules.free I ⟶ M) (i : I) : M.val.obj (op ⊤) :=
  PresheafOfModules.sections.eval (M.freeHomEquiv π i) (op ⊤)

/-- The germ of a global section. -/
abbrev germTop (M : SheafOfModules.{u} Y.ringSheaf) (y : Y) (s : M.val.obj (op ⊤)) :
    (Y.stalkFunctor y).obj M :=
  TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial s

/-- The image of a free generator over an open is the restriction of its global image. -/
lemma eval_freeHomEquiv_eq_map {M : SheafOfModules.{u} Y.ringSheaf} {I : Type u}
    (π : SheafOfModules.free I ⟶ M) (i : I) (U : Opens Y) :
    PresheafOfModules.sections.eval (M.freeHomEquiv π i) (op U) =
      M.val.map (homOfLE le_top : U ⟶ ⊤).op (generatorSection π i) :=
  (PresheafOfModules.sections_property _ _).symm

/-- The germs of the images of the generators of a finite free sheaf span the target stalk of
an epimorphism. -/
theorem span_germ_eq_top {M : SheafOfModules.{u} Y.ringSheaf} {I : Type u} [Finite I]
    (π : SheafOfModules.free I ⟶ M) [Epi π] (y : Y) :
    Submodule.span (Y.presheaf.stalk y)
      (Set.range fun i ↦ germTop M y (generatorSection π i)) = ⊤ := by
  classical
  letI := Fintype.ofFinite I
  rw [eq_top_iff]
  rintro m -
  obtain ⟨U, hyU, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  obtain ⟨S, hS, hlift⟩ := SheafOfModules.exists_app_eq_of_epi π U c
  obtain ⟨V, g, hg, hyV⟩ := hS y hyU
  obtain ⟨a, ha⟩ := hlift g hg
  have h1 : TopCat.Presheaf.germ M.val.presheaf U y hyU c =
      TopCat.Presheaf.germ M.val.presheaf V y hyV (M.val.map g.op c) :=
    (TopCat.Presheaf.germ_res_apply M.val.presheaf g y hyV c).symm
  change _ ∈ _
  rw [h1, ← ha, SheafOfModules.val_app_eq_sum]
  erw [map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  erw [PresheafOfModules.germ_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
  rw [eval_freeHomEquiv_eq_map]
  exact (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE le_top : V ⟶ ⊤) y hyV _).symm

/-- Vanishing of a stalk of a quotient of a finite free sheaf spreads to a neighborhood. -/
theorem exists_forall_subsingleton_stalk {M : SheafOfModules.{u} Y.ringSheaf} {I : Type u}
    [Finite I] (π : SheafOfModules.free I ⟶ M) [Epi π] (y : Y)
    [Subsingleton ((Y.stalkFunctor y).obj M)] :
    ∃ U : Opens Y, y ∈ U ∧ ∀ w ∈ U, Subsingleton ((Y.stalkFunctor w).obj M) := by
  classical
  letI := Fintype.ofFinite I
  have h0 : ∀ i, TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial (generatorSection π i) =
      TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial 0 := fun i ↦
    Subsingleton.elim (α := (Y.stalkFunctor y).obj M) _ _
  choose W hyW iU iV hW using fun i ↦
    TopCat.Presheaf.germ_eq M.val.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ (h0 i)
  refine ⟨⟨⋂ i, ((W i : Opens Y.toPresheafedSpace) : Set Y.toPresheafedSpace),
    isOpen_iInter_of_finite fun i ↦ (W i).isOpen⟩,
    Set.mem_iInter.2 hyW, fun w hw ↦ ?_⟩
  have hwi : ∀ i, w ∈ W i := fun i ↦ Set.mem_iInter.1 hw i
  have hzero : ∀ i, germTop M w (generatorSection π i) = 0 := by
    intro i
    have h1 := TopCat.Presheaf.germ_res_apply M.val.presheaf (iU i) w (hwi i)
      (generatorSection π i)
    have h2 := TopCat.Presheaf.germ_res_apply M.val.presheaf (iV i) w (hwi i) 0
    rw [hW i] at h1
    rw [germTop, ← h1, h2]
    exact map_zero _
  have hspan := span_germ_eq_top π w
  refine ⟨fun a b ↦ ?_⟩
  have hbot : ∀ m : (Y.stalkFunctor w).obj M, m = 0 := by
    intro m
    have hm : m ∈ Submodule.span (Y.presheaf.stalk w)
        (Set.range fun i ↦ germTop M w (generatorSection π i)) := hspan ▸ Submodule.mem_top
    have hle : Submodule.span (Y.presheaf.stalk w)
        (Set.range fun i ↦ germTop M w (generatorSection π i)) ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hzero i
    exact (Submodule.mem_bot _).1 (hle hm)
  rw [hbot a, hbot b]

/-- Formula for a free-sheaf inclusion on sections. -/
lemma ιFree_val_app_eq_smul {I : Type u} (j : I) (W : Opens Y.toPresheafedSpace)
    (r : Y.presheaf.obj (op W)) :
    (SheafOfModules.ιFree (R := Y.ringSheaf) j).val.app (op W) r =
      r • PresheafOfModules.sections.eval
        ((SheafOfModules.free (R := Y.ringSheaf) I).freeHomEquiv (𝟙 _) j) (op W) := by
  have := SheafOfModules.unitHomEquiv_symm_val_app
    (((SheafOfModules.free (R := Y.ringSheaf) I).freeHomEquiv (𝟙 _) j)) (op W) r
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Category.comp_id] at this
  exact this

/-- Germs of the standard generators of a finite free sheaf are linearly independent. -/
theorem linearIndependent_germ_free {I : Type u} [Finite I] (y : Y) :
    LinearIndependent (Y.presheaf.stalk y) (fun i ↦
      germTop (SheafOfModules.free (R := Y.ringSheaf) I) y (generatorSection (𝟙 _) i)) := by
  classical
  letI := Fintype.ofFinite I
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose V hyV a ha using fun j ↦ TopCat.Presheaf.exists_germ_eq Y.presheaf (g j)
  let W : Opens Y.toPresheafedSpace :=
    ⟨⋂ j, ((V j : Opens Y.toPresheafedSpace) : Set Y.toPresheafedSpace),
      isOpen_iInter_of_finite fun j ↦ (V j).isOpen⟩
  have hyW : y ∈ W := Set.mem_iInter.2 hyV
  have hWV : ∀ j, W ≤ V j := fun j _ hz ↦ Set.mem_iInter.1 hz j
  let a' : I → Y.presheaf.obj (op W) := fun j ↦ Y.presheaf.map (homOfLE (hWV j)).op (a j)
  have hga : ∀ j, g j = Y.presheaf.germ W y hyW (a' j) := fun j ↦ by
    rw [← ha j]
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (hWV j)) y hyW (a j)).symm
  let s : (SheafOfModules.free (R := Y.ringSheaf) I).val.obj (op W) :=
    SheafOfModules.freeEvalSymm (op W) a'
  have hs' : TopCat.Presheaf.germ (SheafOfModules.free (R := Y.ringSheaf) I).val.presheaf W y hyW
      s = 0 := by
    refine Eq.trans ?_ hg
    simp only [s, SheafOfModules.freeEvalSymm_apply]
    erw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ιFree_val_app_eq_smul]
    erw [PresheafOfModules.germ_smul]
    rw [hga j, eval_freeHomEquiv_eq_map]
    congr 1
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE le_top : W ⟶ ⊤) y hyW _
  obtain ⟨W', hyW', i₁, i₂, h⟩ := TopCat.Presheaf.germ_eq
    (SheafOfModules.free (R := Y.ringSheaf) I).val.presheaf (U := W) (V := W) y hyW hyW s 0
    (hs'.trans (map_zero _).symm)
  have h' := congrArg (fun t ↦ SheafOfModules.freeEval (R := Y.ringSheaf) (I := I) (op W') t i) h
  erw [SheafOfModules.freeEval_naturality, SheafOfModules.freeEval_naturality] at h'
  rw [SheafOfModules.freeEval_freeEvalSymm] at h'
  have h0 : (SheafOfModules.freeEval (R := Y.ringSheaf) (I := I) (op W)) 0 i = 0 := by
    rw [map_zero]
    rfl
  erw [h0, map_zero] at h'
  rw [hga i, ← TopCat.Presheaf.germ_res_apply Y.presheaf i₁ y hyW']
  erw [h']
  exact map_zero _

/-- The stalk of a finite free sheaf has the basis given by germs of its generators. -/
def basisStalkFree (I : Type u) [Finite I] (y : Y) :
    Module.Basis I (Y.presheaf.stalk y)
      ((Y.stalkFunctor y).obj (SheafOfModules.free (R := Y.ringSheaf) I)) :=
  Module.Basis.mk (linearIndependent_germ_free y) (span_germ_eq_top (𝟙 _) y).ge

lemma basisStalkFree_apply (I : Type u) [Finite I] (y : Y) (i : I) :
    basisStalkFree I y i =
      germTop (SheafOfModules.free (R := Y.ringSheaf) I) y (generatorSection (𝟙 _) i) :=
  Module.Basis.mk_apply _ _ _

/-- A finite free sheaf has free stalks. -/
instance (I : Type u) [Finite I] (y : Y) : Module.Free (Y.presheaf.stalk y)
    ((Y.stalkFunctor y).obj (SheafOfModules.free (R := Y.ringSheaf) I)) :=
  Module.Free.of_basis (basisStalkFree I y)

/-- Stalk maps send a germ to the germ of the image section. -/
lemma stalkFunctor_map_germTop {M N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N) (y : Y)
    (s : M.val.obj (op ⊤)) :
    (Y.stalkFunctor y).map φ (germTop M y s) = germTop N y (φ.val.app (op ⊤) s) :=
  PresheafOfModules.stalkFunctor_map_germ y M.val N.val φ.val ⊤ trivial s

/-- Images of free generators compose. -/
lemma generatorSection_comp {M N : SheafOfModules.{u} Y.ringSheaf} {I : Type u}
    (π : SheafOfModules.free I ⟶ M) (φ : M ⟶ N) (i : I) :
    generatorSection (π ≫ φ) i = φ.val.app (op ⊤) (generatorSection π i) :=
  rfl

/-- The stalk functor is a left adjoint. -/
instance (y : Y) : (Y.stalkFunctor y).IsLeftAdjoint :=
  (SheafOfModules.stalkSkyscraperAdj (hR := Y.isSheaf_ringSheaf) y).isLeftAdjoint

/-- Maps on stalks of a composite which vanishes compose to zero. -/
lemma stalkFunctor_map_map_eq_zero {M N P : SheafOfModules.{u} Y.ringSheaf} (f : M ⟶ N)
    (g : N ⟶ P) (hfg : f ≫ g = 0) (y : Y) (m : (Y.stalkFunctor y).obj M) :
    (Y.stalkFunctor y).map g ((Y.stalkFunctor y).map f m) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hfg, Functor.map_zero]
  rfl

/-- A monomorphism induces an injective map on stalks. -/
lemma injective_stalk_of_mono {M N : SheafOfModules.{u} Y.ringSheaf} (f : M ⟶ N) [Mono f]
    (y : Y) : Function.Injective ((Y.stalkFunctor y).map f) := by
  haveI : (Y.stalkFunctor y).PreservesMonomorphisms :=
    SheafOfModules.preservesMonomorphisms_stalkFunctor (hR := Y.isSheaf_ringSheaf) y
  have : Mono ((Y.stalkFunctor y).map f) := (Y.stalkFunctor y).map_mono f
  exact (ModuleCat.mono_iff_injective _).1 this

/-- An epimorphism induces a surjective map on stalks. -/
lemma surjective_stalk_of_epi {M N : SheafOfModules.{u} Y.ringSheaf} (f : M ⟶ N) [Epi f]
    (y : Y) : Function.Surjective ((Y.stalkFunctor y).map f) := by
  have : Epi ((Y.stalkFunctor y).map f) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

/-- A short exact sequence remains exact on stalks. -/
lemma exact_stalk (S : ShortComplex (SheafOfModules.{u} Y.ringSheaf)) (hS : S.Exact) (y : Y) :
    Function.Exact ((Y.stalkFunctor y).map S.f) ((Y.stalkFunctor y).map S.g) := by
  have h := SheafOfModules.stalk_exact_of_exact S hS y
  rw [ShortComplex.ab_exact_iff] at h
  intro b
  refine ⟨fun hb ↦ h b hb, ?_⟩
  rintro ⟨a, rfl⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, S.zero, Functor.map_zero]
  rfl

/-- Dimension shifting on stalks for a short exact sequence with finite free middle term. -/
lemma hasProjectiveDimensionLE_stalk_of_shortExact {K M : SheafOfModules.{u} Y.ringSheaf}
    {I : Type u} [Finite I] (i : K ⟶ SheafOfModules.free I)
    (p : SheafOfModules.free I ⟶ M) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact) (y : Y) (k : ℕ)
    (h : HasProjectiveDimensionLE ((Y.stalkFunctor y).obj M) (k + 1)) :
    HasProjectiveDimensionLE ((Y.stalkFunctor y).obj K) k := by
  haveI := hS.mono_f
  haveI := hS.epi_g
  haveI : Module.Projective (Y.presheaf.stalk y)
      ((Y.stalkFunctor y).obj (SheafOfModules.free (R := Y.ringSheaf) I)) :=
    Module.Projective.of_free
  exact ModuleCat.hasProjectiveDimensionLE_of_exact ((Y.stalkFunctor y).map i).hom
    ((Y.stalkFunctor y).map p).hom (exact_stalk _ hS.exact y) (injective_stalk_of_mono i y)
    (surjective_stalk_of_epi p y) k

end AlgebraicGeometry.LocallyRingedSpace
