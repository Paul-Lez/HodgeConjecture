/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.OverSpec
public import Other.Oka.AnalyticSpace.OpenSubspace
public import Other.Oka.AnalyticSpace.Nonvanishing

/-!
# The analytification of an open subspace

If `π : W ⟶ Y` is an analytification of `Y`, then for an open `U` of `Y` the preimage of `U` in
`W`, as an open subspace, is an analytification of `Y|U`, by the restriction of `π`.
Consequently the domain of the analytification is closed under open immersions.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

/-- The restriction of an object of `Over specℂ` to an open subset. -/
noncomputable def overRestrict (Y : Over specℂ) (U : Opens Y.left) : Over specℂ :=
  Over.mk (Y.left.ofRestrict U.isOpenEmbedding ≫ Y.hom)

/-- The inclusion of `overRestrict Y U` into `Y`. -/
noncomputable def overRestrictι (Y : Over specℂ) (U : Opens Y.left) : overRestrict Y U ⟶ Y :=
  Over.homMk (Y.left.ofRestrict U.isOpenEmbedding)

@[simp]
lemma overRestrictι_left (Y : Over specℂ) (U : Opens Y.left) :
    (overRestrictι Y U).left = Y.left.ofRestrict U.isOpenEmbedding := rfl

variable {Y : Over specℂ} {W : AnalyticSpace.{u}}

/-- The preimage of an open of `Y` in `W`. -/
noncomputable abbrev preimageOpens (π : toOverSpec.obj W ⟶ Y) (U : Opens Y.left) : W.Opens :=
  (Opens.map π.left.base).obj U

/-- **The restriction of `π : W ⟶ Y` over an open `U` of `Y`**, from the preimage of `U`. -/
noncomputable def restrictπ (π : toOverSpec.obj W ⟶ Y) (U : Opens Y.left) :
    toOverSpec.obj (W.restrict (preimageOpens π U)) ⟶ overRestrict Y U :=
  Over.homMk (ComplexAnalytic.restrictHom π.left U) (by
    have h1 := ComplexAnalytic.restrictHom_fac π.left U =≫ Y.hom
    simp only [Category.assoc, Over.w π] at h1
    exact h1.trans (Over.w (toOverSpec.map (W.ofRestrict (preimageOpens π U)))))

@[simp]
lemma restrictπ_left (π : toOverSpec.obj W ⟶ Y) (U : Opens Y.left) :
    (restrictπ π U).left = ComplexAnalytic.restrictHom π.left U := rfl

@[reassoc]
theorem restrictπ_comp (π : toOverSpec.obj W ⟶ Y) (U : Opens Y.left) :
    restrictπ π U ≫ overRestrictι Y U = toOverSpec.map (W.ofRestrict _) ≫ π := by
  ext1
  exact ComplexAnalytic.restrictHom_fac π.left U

/-- Two morphisms into `overRestrict Y U` agreeing after `overRestrictι` are equal. -/
lemma overRestrict_hom_ext {Z : Over specℂ} (U : Opens Y.left) {f g : Z ⟶ overRestrict Y U}
    (e : f ≫ overRestrictι Y U = g ≫ overRestrictι Y U) : f = g := by
  ext1
  exact LocallyRingedSpace.hom_ext_restrict U _ _ (congrArg CommaMorphism.left e)

instance mono_overRestrictι (U : Opens Y.left) : Mono (overRestrictι Y U) :=
  ⟨fun _ _ e ↦ overRestrict_hom_ext U e⟩

/-- **The analytification of an open subspace is the preimage of it.** -/
theorem IsAnalytification.restrict {π : toOverSpec.obj W ⟶ Y} (h : IsAnalytification π)
    (U : Opens Y.left) : IsAnalytification (restrictπ π U) := by
  intro Z
  refine ⟨fun φ ψ e ↦ ?_, fun f ↦ ?_⟩
  · refine hom_ext_restrict _ _ _ (h.hom_ext ?_)
    have := congrArg (· ≫ overRestrictι Y U) e
    simpa [restrictπ_comp] using this
  · let g := h.lift (f ≫ overRestrictι Y U)
    have hg : Set.range g.toLRSHom.base ⊆ (preimageOpens π U : Set W) := by
      rintro _ ⟨z, rfl⟩
      have e := congrArg (fun m ↦ m.left.base z) (h.lift_fac (f ≫ overRestrictι Y U))
      change π.left.base (g.toLRSHom.base z) ∈ U
      simp only [Over.comp_left, toOverSpec_map_left, LocallyRingedSpace.comp_base,
        TopCat.comp_app] at e
      erw [e]
      exact ((f.left).base z).2
    refine ⟨liftOpen g _ hg, overRestrict_hom_ext U ?_⟩
    rw [Category.assoc, restrictπ_comp, ← Category.assoc, ← Functor.map_comp, liftOpen_fac,
      h.lift_fac]

/-- The open of `Y` which is the range of an open immersion `j : U ⟶ Y`. -/
noncomputable def opensRangeOver {U Y : Over specℂ} (j : U ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j.left] : Opens Y.left :=
  ⟨Set.range j.left.base,
    (PresheafedSpace.IsOpenImmersion.base_open (f := j.left.toHom)).isOpenMap.isOpen_range⟩

/-- **The source of an open immersion is the open subspace on its range**, over `Spec ℂ`. -/
noncomputable def isoOverRestrictOfIsOpenImmersion {U Y : Over specℂ} (j : U ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j.left] : U ≅ overRestrict Y (opensRangeOver j) :=
  have hV := LocallyRingedSpace.isOpenImmersion_ofRestrict Y.left (opensRangeOver j)
  have hr : Set.range j.left.base =
      Set.range (Y.left.ofRestrict (opensRangeOver j).isOpenEmbedding).base := by
    rw [LocallyRingedSpace.range_ofRestrict]; rfl
  Over.isoMk (@LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ _ _ _ _ hV hr) (by
    change _ ≫ Y.left.ofRestrict (opensRangeOver j).isOpenEmbedding ≫ Y.hom = _
    exact (Category.assoc _ _ _).symm.trans
      ((@LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _ _ _ _ hV hr =≫
        Y.hom).trans (Over.w j)))

/-- **The domain of the analytification is closed under open immersions.** -/
theorem rightAdjointObjIsDefined_of_isOpenImmersion {U Y : Over specℂ} (j : U ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j.left] (h : toOverSpec.rightAdjointObjIsDefined Y) :
    toOverSpec.rightAdjointObjIsDefined U := by
  obtain ⟨W, π, hπ⟩ := exists_isAnalytification h
  exact rightAdjointObjIsDefined_of_iso (isoOverRestrictOfIsOpenImmersion j).symm
    (hπ.restrict _).rightAdjointObjIsDefined

end ComplexAnalytic

end
