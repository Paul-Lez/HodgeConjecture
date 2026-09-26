/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.Tilde

/-!
# Exactness of `M ↦ M^~`, and finiteness of sections of restrictions to affine opens

For a commutative ring `R`:

* `AlgebraicGeometry.tilde.mono_map`: `M^~ ⟶ N^~` is a monomorphism for an injective
  `f : M ⟶ N`, since on sections over `U` it is the map induced by the injective maps
  `M_𝔭 → N_𝔭` of localisations
  (`AlgebraicGeometry.StructureSheaf.Localizations.comapFun_injective`).
  Being a left adjoint, `M ↦ M^~` is also right exact, so it is exact:
  `AlgebraicGeometry.tilde.shortExact_map` sends short exact sequences of `R`-modules to short
  exact sequences of `𝒪_{Spec R}`-modules.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorEquivOfIso`: restriction along an isomorphism
  of schemes is an equivalence of categories of modules (in particular exact).
* `AlgebraicGeometry.Scheme.Modules.module_finite_Γ_restrict`: for an open immersion
  `j : Spec R ⟶ X` and a quasi-coherent `𝒪_X`-module `F` of finite type, the global sections of
  `j^* F` form a finite `R`-module. Locally on `Spec R` the image of a basic open `D(g)` is an
  affine open on which `F` has finitely many generating sections, so `Γ(j^* F, D(g))` is finite over
  `Γ(Spec R, D(g))`; these are the localisations of `Γ(j^* F)` for finitely many `g` spanning the
  unit ideal.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry

namespace StructureSheaf

/-- The map of localisations `M_𝔭 → N_𝔭` induced by an injective linear map is injective. -/
lemma Localizations.comapFun_injective {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Injective f) (y : PrimeSpectrum R) :
    Function.Injective (Localizations.comapFun f y) := by
  intro a b hab
  induction a using LocalizedModule.induction_on with | h a s => ?_
  induction b using LocalizedModule.induction_on with | h b t => ?_
  rw [Localizations.comapFun_mk, Localizations.comapFun_mk, LocalizedModule.mk_eq] at hab
  obtain ⟨c, hc⟩ := hab
  rw [LocalizedModule.mk_eq]
  refine ⟨⟨c.1, c.2⟩, hf ?_⟩
  simp only [Submonoid.smul_def, map_smul] at hc ⊢
  exact hc

end StructureSheaf

namespace tilde

variable {R : CommRingCat.{u}}

/-- For an injective `f : M ⟶ N`, the map `M^~ ⟶ N^~` is injective on sections. -/
lemma injective_map_app {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Injective f)
    (p : (Spec R).Opensᵒᵖ) : Function.Injective ((tilde.map f).val.app p) := by
  intro x y h
  apply Subtype.ext
  funext z
  exact StructureSheaf.Localizations.comapFun_injective f.hom hf z.1
    (congrArg (fun s => s.1 z) h)

/-- For an injective `f : M ⟶ N`, the map `M^~ ⟶ N^~` is a monomorphism. -/
lemma mono_map {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Injective f) :
    Mono (tilde.map f) := by
  let G := SheafOfModules.forget (Spec R).ringCatSheaf ⋙ PresheafOfModules.toPresheaf _
  have : Mono (G.map (tilde.map f)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro p
    rw [AddCommGrpCat.mono_iff_injective]
    exact injective_map_app f hf p
  exact G.mono_of_mono_map this

/-- **`M ↦ M^~` is exact**: it sends short exact sequences of `R`-modules to short exact
sequences of `𝒪_{Spec R}`-modules. -/
lemma shortExact_map {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.map (tilde.functor R)).ShortExact where
  exact := hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance
  mono_f := mono_map S.f ((ModuleCat.mono_iff_injective _).1 hS.mono_f)
  epi_g := by haveI := hS.epi_g; exact (tilde.functor R).map_epi S.g

end tilde

namespace Scheme.Modules

/-- **Restriction along an isomorphism of schemes is an equivalence** of categories of modules,
with inverse the restriction along the inverse isomorphism. -/
def restrictFunctorEquivOfIso {Y Z : Scheme.{u}} (e : Y ≅ Z) : Z.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    (restrictFunctorId.symm ≪≫ restrictFunctorCongr e.inv_hom_id.symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId)

instance {Y Z : Scheme.{u}} (e : Y ≅ Z) : (restrictFunctor e.hom).IsEquivalence :=
  (restrictFunctorEquivOfIso e).isEquivalence_functor

/-- **Finiteness of the sections of a module is finiteness of the sections of its restriction**:
the converse of `AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict`, again
`Module.Finite.of_ringEquiv` along `AlgebraicGeometry.Scheme.Hom.appIso`. -/
theorem module_finite_restrict_sections {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
    (M : W.Modules) (U : V.Opens) [Module.Finite Γ(W, f ''ᵁ U) Γ(M, f ''ᵁ U)] :
    Module.Finite Γ(V, U) Γ(M.restrict f, U) := by
  letI : Module Γ(W, f ''ᵁ U) Γ(M.restrict f, U) :=
    inferInstanceAs (Module Γ(W, f ''ᵁ U) Γ(M, f ''ᵁ U))
  haveI : Module.Finite Γ(W, f ''ᵁ U) Γ(M.restrict f, U) :=
    inferInstanceAs (Module.Finite Γ(W, f ''ᵁ U) Γ(M, f ''ᵁ U))
  refine Module.Finite.of_ringEquiv (f.appIso U).commRingCatIsoToRingEquiv fun a n ↦ ?_
  have := smul_restrictAppIso_hom_apply f M U ((f.appIso U).hom a) n
  rw [Iso.hom_inv_id_apply] at this
  exact this.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The global sections of the restriction of a quasi-coherent sheaf of finite type along an
open immersion `j : Spec R ⟶ X` are a finite `R`-module.**

Every point of `Spec R` has a basic open neighbourhood `D(g)` whose image `j(D(g))`, an affine
open of `X`, lies in a member of a covering over which `F` has finitely many generating
sections; so `Γ(F, j(D(g)))` is finite over `Γ(X, j(D(g)))`
(`AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_isAffineOpen`), i.e.
`Γ(j^* F, D(g))` is finite over `Γ(Spec R, D(g))`. Finitely many such `g` span the unit ideal,
and `Γ(j^* F, D(g))` is the localisation of `Γ(j^* F)` away from `g`
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen`), so
`Module.Finite.of_localizationSpan_finite'` applies. -/
theorem module_finite_Γ_restrict {X : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ X)
    [IsOpenImmersion j] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite R (moduleSpecΓFunctor.obj (F.restrict j) : Type u) := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u, u} F
  have hcov : ⨆ i, σ.X i = ⊤ := (Opens.coversTop_iff (U := σ.X) _).1 σ.coversTop
  have htop : (⨆ g : {g : R // ∃ i, (PrimeSpectrum.basicOpen g : (Spec R).Opens) ≤ j ⁻¹ᵁ σ.X i},
      (PrimeSpectrum.basicOpen g.1 : (Spec R).Opens)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : j.base x ∈ ⨆ i, σ.X i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    obtain ⟨V, ⟨g, rfl⟩, hxV, hV⟩ :=
      Opens.isBasis_iff_nbhd.1 PrimeSpectrum.isBasis_basic_opens
        (show x ∈ j ⁻¹ᵁ σ.X i from hi)
    exact Opens.mem_iSup.2 ⟨⟨g, i, hV⟩, hxV⟩
  rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff] at htop
  obtain ⟨s, hsub, hs1⟩ :=
    Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 htop)
  have hs : Ideal.span (s : Set R) = ⊤ := (Ideal.eq_top_iff_one _).2 hs1
  set N := F.restrict j
  have hfin : ∀ g ∈ s, Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen g)
      Γ(N, PrimeSpectrum.basicOpen g) := by
    intro g hg
    obtain ⟨⟨g', i, hi⟩, rfl⟩ := hsub hg
    haveI := hσ.isFiniteType i
    let τ := SheafOfModules.GeneratingSections.restrict.{u}
      (homOfLE ((j.image_mono hi).trans (j.image_preimage_le _))) (σ.generators i)
    haveI : Finite τ.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
    haveI := module_finite_sections_of_isAffineOpen F
      ((IsAffineOpen.Spec_basicOpen g').image_of_isOpenImmersion j) τ
    exact module_finite_restrict_sections j F _
  haveI : ∀ g : s, IsLocalizedModule.Away (g : R) (sectionsToBasicOpen N (g : R)).hom :=
    fun g ↦ isLocalizedModule_away_sectionsToBasicOpen N (g : R)
  letI : ∀ g : s, Module Γ(Spec R, PrimeSpectrum.basicOpen (g : R))
      ((modulesSpecToSheaf.obj N).presheaf.obj (op (PrimeSpectrum.basicOpen (g : R))) : Type u) :=
    fun g ↦ inferInstanceAs (Module Γ(Spec R, PrimeSpectrum.basicOpen (g : R))
      Γ(N, PrimeSpectrum.basicOpen (g : R)))
  haveI : ∀ g : s, IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen (g : R))
      ((modulesSpecToSheaf.obj N).presheaf.obj (op (PrimeSpectrum.basicOpen (g : R))) : Type u) :=
    fun g ↦ inferInstanceAs (IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen (g : R))
      Γ(N, PrimeSpectrum.basicOpen (g : R)))
  refine Module.Finite.of_localizationSpan_finite' s hs
    (Rₚ := fun g ↦ Γ(Spec R, PrimeSpectrum.basicOpen (g : R)))
    (fun g ↦ (sectionsToBasicOpen N (g : R)).hom) fun g ↦ ?_
  exact hfin g g.2

end Scheme.Modules

end AlgebraicGeometry

end

end
