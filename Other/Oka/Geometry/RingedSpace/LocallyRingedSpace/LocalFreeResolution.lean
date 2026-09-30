/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Free
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Coherent
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.LocallyFree
public import Other.Oka.RingTheory.Regular.ChangeOfRings

/-!
# Local finite free resolutions of coherent sheaves

Let `Y` be a locally ringed space whose structure sheaf is coherent in the local form
`AlgebraicGeometry.LocallyRingedSpace.HasLocalRelations` (which passes to open subspaces), and let
`M` be a coherent sheaf of `𝒪_Y`-modules.

- `AlgebraicGeometry.LocallyRingedSpace.exists_hasFreeResolutionLE_of_stalk`: if the stalk `M_y`
  has projective dimension `≤ k`, then `M|_U` has a finite free resolution of length `≤ k` on some
  open `U ∋ y`.
- `AlgebraicGeometry.LocallyRingedSpace.exists_hasFreeResolutionLE`: if every finitely generated
  module over every stalk `𝒪_{Y, y}` has projective dimension `≤ n` (for a complex manifold of
  dimension `n`: the analytic syzygy theorem), then every point has an open neighbourhood `U` on
  which `M|_U` has a finite free resolution `0 → 𝒪^{pₙ} → ⋯ → 𝒪^{p₀} → M|_U → 0`.

The proof is by induction on `k`. For `k = 0`, `M_y` is a finitely generated projective module
over a local ring, hence free, and a coherent sheaf with free stalk is free near `y`
(`AlgebraicGeometry.LocallyRingedSpace.exists_hasFreeResolutionLE_zero`). For the inductive step,
choose an epimorphism `𝒪^I ⟶ M|_U` near `y`; its kernel `K` is coherent (Oka's theorem on `Y`
enters through the coherence of `𝒪^I`), and `K_y` has projective dimension `≤ k` by dimension
shifting (`AlgebraicGeometry.LocallyRingedSpace.hasProjectiveDimensionLE_stalk_of_shortExact`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite Limits

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The kernel of an epimorphism, as a short exact sequence. -/
lemma shortExact_kernel {C : Type*} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y) [Epi f] :
    (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)

/-- **Local free resolutions from projective dimension of the stalk.** If `Y` has locally finitely
generated relations, `M` is coherent and `M_y` has projective dimension `≤ k`, then `M|_U` has a
finite free resolution of length `≤ k` for some open `U ∋ y`. -/
theorem exists_hasFreeResolutionLE_of_stalk (k : ℕ) :
    ∀ {Y : LocallyRingedSpace.{u}} (_ : Y.HasLocalRelations) (M : SheafOfModules.{u} Y.ringSheaf)
      [M.IsCoherent] (y : Y), HasProjectiveDimensionLE ((Y.stalkFunctor y).obj M) k →
      ∃ (U : Opens Y) (_ : y ∈ U), ((Y.restrictModules U).obj M).HasFreeResolutionLE k := by
  induction k with
  | zero =>
    intro Y _ M _ y h
    exact exists_hasFreeResolutionLE_zero M y h
  | succ k ih =>
    intro Y hY M _ y h
    obtain ⟨U, hyU, I, _, π, _⟩ := exists_epi_free_restrictModules M y
    let Y' := Y.restrict U.isOpenEmbedding
    let M' := (Y.restrictModules U).obj M
    let y' : Y' := ⟨y, hyU⟩
    have hY' : Y'.HasLocalRelations := hY.restrict U
    haveI : (SheafOfModules.unit Y'.ringSheaf).IsCoherent :=
      isCoherentStructureSheaf_of_hasLocalRelations hY'
    haveI : (SheafOfModules.free (R := Y'.ringSheaf) I).IsCoherent :=
      SheafOfModules.IsCoherent.free I
    haveI : M'.IsCoherent := isCoherent_restrictModules M U
    haveI : (kernel π).IsCoherent := SheafOfModules.IsCoherent.kernel π
    have hpd : HasProjectiveDimensionLE ((Y'.stalkFunctor y').obj M') (k + 1) :=
      @Hom.hasProjectiveDimensionLE_stalk_pullbackModules _ _ (Y.ofRestrict U.isOpenEmbedding)
        y' _ M (k + 1) h
    have hS := shortExact_kernel π
    have hK := hasProjectiveDimensionLE_stalk_of_shortExact _ _ _ hS y' k hpd
    obtain ⟨V, hyV, hV⟩ := ih hY' (kernel π) y' hK
    haveI : PreservesFiniteLimits (Y'.restrictModules V) :=
      (Y'.ofRestrict V.isOpenEmbedding).preservesFiniteLimits_pullbackModules
        (flat_stalkMap_of_isIso _)
    haveI : (Y'.restrictModules V).IsLeftAdjoint :=
      (Y'.ofRestrict V.isOpenEmbedding).pullbackModulesAdj.isLeftAdjoint
    haveI : PreservesColimits (Y'.restrictModules V) :=
      (Y'.ofRestrict V.isOpenEmbedding).pullbackModulesAdj.leftAdjoint_preservesColimits
    haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint (Y'.restrictModules V)
    have hres : ((Y'.restrictModules V).obj M').HasFreeResolutionLE (k + 1) :=
      .of_shortExact_map _ (fun I _ ↦ (Y'.ofRestrict V.isOpenEmbedding).pullbackModulesFreeIso I)
        _ _ _ hS hV
    exact ⟨imOpen U V, mem_imOpen U V hyU hyV,
      hasFreeResolutionLE_restrictModules_of_restrict U V hres⟩

/-- **Local finite free resolutions of coherent sheaves.** Let `Y` be a locally ringed space with
locally finitely generated relations, all of whose stalks have the property that every finitely
generated module has projective dimension `≤ n`. Then every coherent sheaf of modules `M` has,
near every point `y`, a finite free resolution of length `≤ n`. -/
theorem exists_hasFreeResolutionLE {Y : LocallyRingedSpace.{u}} (hY : Y.HasLocalRelations)
    {n : ℕ} (hdim : ∀ y : Y, ModuleCat.HasFGGlobalDimensionLE (Y.presheaf.stalk y) n)
    (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent] (y : Y) :
    ∃ (U : Opens Y) (_ : y ∈ U), ((Y.restrictModules U).obj M).HasFreeResolutionLE n := by
  obtain ⟨U, hyU, I, _, π, _⟩ := exists_epi_free_restrictModules M y
  let Y' := Y.restrict U.isOpenEmbedding
  let M' := (Y.restrictModules U).obj M
  let y' : Y' := ⟨y, hyU⟩
  haveI : M'.IsCoherent := isCoherent_restrictModules M U
  have hspan := span_germ_eq_top π y'
  haveI : Module.Finite (Y'.presheaf.stalk y') ((Y'.stalkFunctor y').obj M') := by
    haveI := Fintype.ofFinite I
    refine ⟨⟨(Set.finite_range fun i ↦ germTop M' y' (generatorSection π i)).toFinset, ?_⟩⟩
    rw [Set.Finite.coe_toFinset]
    exact hspan
  have hdim' : ModuleCat.HasFGGlobalDimensionLE (Y'.presheaf.stalk y') n :=
    (hdim y).of_ringEquiv ((Y.ofRestrict U.isOpenEmbedding).stalkMapRingEquiv y')
  obtain ⟨V, hyV, hV⟩ := exists_hasFreeResolutionLE_of_stalk n (hY.restrict U) M' y'
    (hdim' ((Y'.stalkFunctor y').obj M'))
  exact ⟨imOpen U V, mem_imOpen U V hyU hyV,
    hasFreeResolutionLE_restrictModules_of_restrict U V hV⟩

end AlgebraicGeometry.LocallyRingedSpace

end
