/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Other.Oka.AlgebraicGeometry.Modules.Tilde
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwist
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.LocallySurjective

/-!
# Sections of quasi-coherent sheaves over basic opens of affine opens

Let `F` be a quasi-coherent `𝒪_X`-module, `U ⊆ X` an affine open and `f ∈ Γ(X, U)`. The
restriction `Γ(F, U) → Γ(F, D(f))` is the localisation away from `f`, which we record in the two
elementwise forms used in extension arguments (e.g. Serre's theorem A):

- `IsAffineOpen.exists_restrictOpen_eq_pow_smul`: every `s ∈ Γ(F, D(f))` has `fᵏ s` extending to
  a section over `U`;
- `IsAffineOpen.exists_pow_smul_eq_zero`: a section over `U` vanishing on `D(f)` is killed by a
  power of `f`.

Both are transported from `Spec Γ(X, U)` along `IsAffineOpen.fromSpec`
(`Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen`).

We also prove:

- `IsAffineOpen.exists_module_finite_basicOpen`: if `F` is moreover of finite type, every point of
  `U` has a basic open neighbourhood `D(g) ⊆ U` with `Γ(F, D(g))` finite over `Γ(X, D(g))`.
- `Scheme.Modules.epi_of_forall_exists`: a morphism of `𝒪_X`-modules which is locally surjective
  on sections is an epimorphism.
- `Scheme.Modules.epi_of_surjective_app_affine`: a morphism `M ⟶ N` which is surjective on the
  sections over the members of an affine open cover is an epimorphism, provided `N` satisfies the
  extension property above on these affine opens.
- `Scheme.Modules.freeMk`: the morphism `free I ⟶ M` given by a family of global sections.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

lemma Scheme.basicOpen_restrictOpen {V W : X.Opens} (h : W ≤ V) (f : Γ(X, V)) :
    X.basicOpen (TopCat.Presheaf.restrictOpen f W h) = W ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

namespace Scheme.Modules

lemma mres_sub (M : X.Modules) {V W : X.Opens} (h : W ≤ V) (x y : Γ(M, V)) :
    TopCat.Presheaf.restrictOpen (x - y) W h =
      TopCat.Presheaf.restrictOpen x W h - TopCat.Presheaf.restrictOpen y W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma ores_pow {V W : X.Opens} (h : W ≤ V) (r : Γ(X, V)) (k : ℕ) :
    TopCat.Presheaf.restrictOpen (r ^ k) W h = TopCat.Presheaf.restrictOpen r W h ^ k := by
  induction k with
  | zero => simp only [pow_zero, ores_one]
  | succ k ih => rw [pow_succ, ores_mul, ih, pow_succ]

end Scheme.Modules

namespace IsAffineOpen

variable {U : X.Opens} (hU : IsAffineOpen U) (F : X.Modules)

lemma fromSpec_image_le (W : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ W ≤ U :=
  (hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le

lemma le_fromSpec_image_top : U ≤ hU.fromSpec ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

set_option backward.isDefEq.respectTransparency false in
/-- Under `fromSpec`, restricting `r ∈ Γ(X, U)` to the image of `W` is restricting
`r ∈ Γ(Spec Γ(X, U), ⊤)` to `W`. -/
lemma fromSpec_appIso_hom_restrict (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso W).hom (X.presheaf.map (homOfLE (hU.fromSpec_image_le W)).op r) =
      (Spec Γ(X, U)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r) := by
  rw [Scheme.Hom.appIso_hom, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, hU.fromSpec_app_of_le U le_rfl]
  simp only [Category.assoc, ← Functor.map_comp, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `Γ(X, U)`-action on the sections of `F|_{Spec Γ(X, U)}` over `W` is the action of the
restriction to `fromSpec ''ᵁ W`. -/
lemma smul_restrict_fromSpec (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (x : Γ(F.restrict hU.fromSpec, W)) :
    (r • x : Γ(F.restrict hU.fromSpec, W)) = (show Γ(F, hU.fromSpec ''ᵁ W) from
      TopCat.Presheaf.restrictOpen r _ (hU.fromSpec_image_le W) •
        (show Γ(F, hU.fromSpec ''ᵁ W) from x)) := by
  rw [Scheme.Modules.smul_Spec_def]
  change _ = X.presheaf.map (homOfLE (hU.fromSpec_image_le W)).op r • _
  rw [← fromSpec_appIso_hom_restrict]
  change ((hU.fromSpec.appIso W).inv ((hU.fromSpec.appIso W).hom _)) •
    (show Γ(F, hU.fromSpec ''ᵁ W) from x) = _
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply]

variable [F.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency false in
include hU in
/-- **Extension of sections from a basic open.** For a quasi-coherent `F`, an affine open `U`
and `f ∈ Γ(X, U)`, every `s ∈ Γ(F, D(f))` has some `fᵏ s` extending to a section over `U`. -/
theorem exists_restrictOpen_eq_pow_smul (f : Γ(X, U)) (s : Γ(F, X.basicOpen f)) :
    ∃ (k : ℕ) (t : Γ(F, U)), TopCat.Presheaf.restrictOpen t (X.basicOpen f) (X.basicOpen_le f) =
      TopCat.Presheaf.restrictOpen f (X.basicOpen f) (X.basicOpen_le f) ^ k • s := by
  have hW := hU.fromSpec_image_basicOpen f
  have h := Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen
    (F.restrict hU.fromSpec) f
  let s' : Γ(F, hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f) :=
    TopCat.Presheaf.restrictOpen s _ hW.le
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (Scheme.Modules.sectionsToBasicOpen (F.restrict hU.fromSpec) f).hom s'
  refine ⟨k, TopCat.Presheaf.restrictOpen (show Γ(F, hU.fromSpec ''ᵁ ⊤) from a) U
    hU.le_fromSpec_image_top, ?_⟩
  have ha' : TopCat.Presheaf.restrictOpen (show Γ(F, hU.fromSpec ''ᵁ ⊤) from a)
      (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f) (hU.fromSpec.image_mono le_top) =
      TopCat.Presheaf.restrictOpen f (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
        (hU.fromSpec_image_le _) ^ k • s' := by
    rw [← ores_pow]
    refine ha.symm.trans ?_
    rw [Submonoid.smul_def]
    exact smul_restrict_fromSpec hU F _ _ _
  refine (mres_res F _ _ _).trans ?_
  refine (mres_res F (hU.fromSpec.image_mono le_top) hW.ge _).symm.trans ?_
  rw [ha', mres_smul, ores_pow, ores_res]
  simp only [s', mres_res, mres_self]

set_option backward.isDefEq.respectTransparency false in
include hU in
/-- **Sections vanishing on a basic open.** For a quasi-coherent `F`, an affine open `U` and
`f ∈ Γ(X, U)`, a section over `U` whose restriction to `D(f)` vanishes is killed by a power
of `f`. -/
theorem exists_pow_smul_eq_zero (f : Γ(X, U)) (t : Γ(F, U))
    (ht : TopCat.Presheaf.restrictOpen t (X.basicOpen f) (X.basicOpen_le f) = 0) :
    ∃ k : ℕ, f ^ k • t = 0 := by
  have hW := hU.fromSpec_image_basicOpen f
  have h := Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen
    (F.restrict hU.fromSpec) f
  let t' : Γ(F, hU.fromSpec ''ᵁ ⊤) := TopCat.Presheaf.restrictOpen t _ (hU.fromSpec_image_le ⊤)
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
    (f := (Scheme.Modules.sectionsToBasicOpen (F.restrict hU.fromSpec) f).hom)
    (x₁ := t') (x₂ := 0) (by
      rw [map_zero]
      change TopCat.Presheaf.restrictOpen t' (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
        (hU.fromSpec.image_mono le_top) = 0
      simp only [t', mres_res]
      rw [← mres_res F (X.basicOpen_le f) hW.le, ht, mres_zero])
  refine ⟨k, ?_⟩
  rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero] at hc
  have hc' := smul_restrict_fromSpec hU F ⊤ (f ^ k) t'
  have h0 : TopCat.Presheaf.restrictOpen (f ^ k) _ (hU.fromSpec_image_le ⊤) • t' = 0 :=
    hc'.symm.trans hc
  apply mres_injective_of_le F (hU.fromSpec_image_le ⊤) hU.le_fromSpec_image_top
  simp only
  rw [mres_smul, h0, mres_zero]

include hU in
/-- For a quasi-coherent `F` of finite type and an affine open `U`, every point of `U` has a
basic open neighbourhood `D(g) ⊆ U` with `Γ(F, D(g))` a finite `Γ(X, D(g))`-module. -/
theorem exists_module_finite_basicOpen [F.IsFiniteType] (x : X) (hx : x ∈ U) :
    ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧
      Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u} F
  have hcov : ⨆ i, σ.X i = ⊤ := (Opens.coversTop_iff (U := σ.X) _).1 σ.coversTop
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ x))
  obtain ⟨g, hg, hxg⟩ := hU.exists_basicOpen_le (V := σ.X i) ⟨x, hi⟩ hx
  haveI := hσ.isFiniteType i
  let τ := SheafOfModules.GeneratingSections.restrict.{u} (homOfLE hg) (σ.generators i)
  haveI : Finite τ.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  exact ⟨g, hxg, Scheme.Modules.module_finite_sections_of_isAffineOpen F (hU.basicOpen g) τ⟩

end IsAffineOpen

namespace Scheme.Modules

/-- A morphism of `𝒪_X`-modules which is locally surjective on sections is an epimorphism. -/
theorem epi_of_forall_exists {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (W : X.Opens) (t : Γ(N, W)) (x : X), x ∈ W → ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧
      ∃ s : Γ(M, V), φ.app V s = TopCat.Presheaf.restrictOpen t V hV) : Epi φ := by
  refine (SheafOfModules.isLocallySurjective_toSheaf_map_iff_epi (M := M) (N := N) φ).1 ?_
  change TopCat.Presheaf.IsLocallySurjective _
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W t x hx
  obtain ⟨V, hV, hxV, s, hs⟩ := h W t x hx
  exact ⟨V, hV, ⟨s, hs⟩, hxV⟩

/-- **Epimorphisms from surjectivity on an affine cover.** Let `V a` be affine opens covering `X`
such that sections of `N` over basic opens `D(f) ⊆ V a` extend to `V a` after multiplication by a
power of `f`. A morphism `M ⟶ N` surjective on sections over every `V a` is an epimorphism. -/
theorem epi_of_surjective_app_affine {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type*} (V : ι → X.Opens) (hcov : ⨆ a, V a = ⊤) (hV : ∀ a, IsAffineOpen (V a))
    (hN : ∀ a (f : Γ(X, V a)) (s : Γ(N, X.basicOpen f)), ∃ (k : ℕ) (t : Γ(N, V a)),
      TopCat.Presheaf.restrictOpen t (X.basicOpen f) (X.basicOpen_le f) =
        TopCat.Presheaf.restrictOpen f (X.basicOpen f) (X.basicOpen_le f) ^ k • s)
    (hsurj : ∀ a, Function.Surjective (φ.app (V a))) : Epi φ := by
  refine epi_of_forall_exists φ fun W t x hx ↦ ?_
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  obtain ⟨f, hfW, hxf⟩ := (hV a).exists_basicOpen_le (V := W) ⟨x, hx⟩ ha
  refine ⟨X.basicOpen f, hfW, hxf, ?_⟩
  obtain ⟨k, u, hu⟩ := hN a f (TopCat.Presheaf.restrictOpen t _ hfW)
  obtain ⟨y, rfl⟩ := hsurj a u
  have hc : IsUnit (TopCat.Presheaf.restrictOpen f (X.basicOpen f) (X.basicOpen_le f) ^ k) :=
    (X.toRingedSpace.isUnit_res_basicOpen f).pow k
  refine ⟨(↑hc.unit⁻¹ : Γ(X, X.basicOpen f)) •
    TopCat.Presheaf.restrictOpen y _ (X.basicOpen_le f), ?_⟩
  rw [Scheme.Modules.Hom.app_smul, Hom.app_mres, hu, smul_smul]
  rw [IsUnit.val_inv_mul, one_smul]

/-- The morphism `free I ⟶ M` given by global sections `σ q ∈ Γ(M, ⊤)`. -/
noncomputable def freeMk (M : X.Modules) {I : Type u} (σ : I → Γ(M, ⊤)) :
    (SheafOfModules.free I : X.Modules) ⟶ M :=
  (SheafOfModules.freeHomEquiv M).symm fun q ↦
    SheafOfModules.sectionOfTerminal Limits.isTerminalTop M (σ q)

/-- `freeMk M σ` sends the `p`-th basis section over `W` to the restriction of `σ p`. -/
lemma freeMk_app_freeSection (M : X.Modules) {I : Type u} (σ : I → Γ(M, ⊤)) (p : I)
    (W : X.Opens) :
    Hom.app (freeMk M σ) W (PresheafOfModules.sections.eval
      (SheafOfModules.freeSection (R := X.ringCatSheaf) p) (op W)) =
      TopCat.Presheaf.restrictOpen (σ p) W le_top := by
  have := congrArg (fun s ↦ PresheafOfModules.sections.eval s (op W))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (M := M) (fun q ↦
      SheafOfModules.sectionOfTerminal Limits.isTerminalTop M (σ q)) p)
  exact this

end Scheme.Modules

end AlgebraicGeometry

end
