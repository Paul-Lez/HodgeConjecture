/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Other.Oka.Topology.Sheaves.Cohomology.ClosedEmbeddingOpen
public import Other.Oka.Topology.Sheaves.Cohomology.OpenEmbedding

/-!
# Underlying abelian sheaves of sheaves of modules on schemes

For a sheaf of modules `M` on a scheme `X`, the underlying abelian sheaf is
`(SheafOfModules.toSheaf X.ringCatSheaf).obj M`, with sections `Γ(M, V)` over `V`. We identify the
underlying abelian sheaves of pushforwards and restrictions of modules with the pushforwards and
restrictions of the underlying abelian sheaves, and deduce comparisons of cohomology on opens.

## Main results

- `AlgebraicGeometry.Scheme.Modules.toAbPushforwardIso`: the underlying abelian sheaf of
  `φ_* M` is `φ_*` of the underlying abelian sheaf of `M`.
- `AlgebraicGeometry.Scheme.Modules.toAbRestrictIso`: the underlying abelian sheaf of
  `M.restrict e` is the restriction `TopCat.Sheaf.restrictAb` of that of `M`.
- `AlgebraicGeometry.Scheme.Modules.hRestrictOpenRestrictAddEquiv`: for an open immersion
  `e : Y ⟶ X` and `W ≤ e.opensRange`, `Hᵠ(W, M) ≃+ Hᵠ(e⁻¹(W), M.restrict e)`.
- `AlgebraicGeometry.Scheme.Modules.hRestrictOpenPushforwardAddEquiv`: for a closed immersion
  `ι : Z ⟶ X`, `Hᵠ(ι⁻¹(W), N) ≃+ Hᵠ(W, ι_* N)`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The underlying abelian sheaf of the pushforward `φ_* M` is the pushforward of the underlying
abelian sheaf of `M`. -/
noncomputable def toAbPushforwardIso (φ : Y ⟶ X) (M : Y.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pushforward φ).obj M) ≅
      (TopCat.Sheaf.pushforwardAb φ.base).obj ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) :=
  Iso.refl _

/-- The underlying abelian sheaf of the restriction of `M` along an open immersion `e` is the
restriction of the underlying abelian sheaf of `M`. -/
noncomputable def toAbRestrictIso (e : Y ⟶ X) [IsOpenImmersion e] (M : X.Modules) :
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj (M.restrict e) ≅
      (TopCat.Sheaf.restrictAb e.isOpenEmbedding).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
  Iso.refl _

/-- For an open immersion `e : Y ⟶ X` and an open `W ≤ e.opensRange`, the cohomology of `M` on
`W` is the cohomology of `M.restrict e` on `e⁻¹(W)`. -/
noncomputable def hRestrictOpenRestrictAddEquiv (e : Y ⟶ X) [IsOpenImmersion e]
    (M : X.Modules) (W : X.Opens) (hW : W ≤ e.opensRange) (q : ℕ) :
    TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) q ≃+
      TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (e ⁻¹ᵁ W)).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj (M.restrict e))) q :=
  (TopCat.Sheaf.H.restrictOpenAddEquivOfEq e.isOpenEmbedding (e ⁻¹ᵁ W) _ q
      ((e.image_preimage_eq_opensRange_inf W).trans (inf_eq_right.2 hW))).trans
    (TopCat.Sheaf.H.restrictOpenAddEquivOfIso (e ⁻¹ᵁ W) (toAbRestrictIso e M).symm q)

/-- For a closed immersion `ι : Z ⟶ X` and an open `W` of `X`, the cohomology of `N` on
`ι⁻¹(W)` is the cohomology of the pushforward `ι_* N` on `W`. -/
noncomputable def hRestrictOpenPushforwardAddEquiv (ι : Z ⟶ X) [IsClosedImmersion ι]
    (N : Z.Modules) (W : X.Opens) (q : ℕ) :
    TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (ι ⁻¹ᵁ W)).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj N)) q ≃+
      TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pushforward ι).obj N))) q :=
  (TopCat.Sheaf.H.restrictOpenPushforwardClosedEmbeddingAddEquiv ι.isClosedEmbedding _ W q).trans
    (TopCat.Sheaf.H.restrictOpenAddEquivOfIso W (toAbPushforwardIso ι N).symm q)

end AlgebraicGeometry.Scheme.Modules

end
