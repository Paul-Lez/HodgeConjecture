/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Coherent
public import Other.Oka.AnalyticSpace.GermGlobalDimension
public import Other.Oka.AnalyticSpace.Relations
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceAn
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.LocalFreeResolution
public import Other.Oka.StalkEquiv

/-!
# Local finite free resolutions of coherent analytic sheaves

On a complex manifold of dimension `n` every coherent sheaf of modules `M` has, near every point,
a finite free resolution `0 → 𝒪^{pₙ} → ⋯ → 𝒪^{p₀} → M|_U → 0` of length `≤ n`, in the sense of
`SheafOfModules.HasFreeResolutionLE`.

The general statement `AlgebraicGeometry.LocallyRingedSpace.exists_hasFreeResolutionLE` needs two
inputs: coherence of the structure sheaf in the form `HasLocalRelations` (Oka's theorem,
`ComplexAnalytic.AnalyticSpace.hasLocalRelations`) and the bound `n` on the projective dimension
of finitely generated modules over the stalks, which for the germ ring of `ℂⁿ` is
`LocalOkaRing.hasFGGlobalDimensionLE`. Both are local and pass along open immersions.

## Main results

- `ComplexAnalytic.exists_hasFreeResolutionLE_complexAffineSpace`: on `ℂⁿ`.
- `ComplexAnalytic.exists_hasFreeResolutionLE_complexAffineSpace_restrict`: on an open subset of
  `ℂⁿ`.
- `ComplexAnalytic.AnalyticSpace.exists_hasFreeResolutionLE`: on an analytic space all of whose
  stalks have finitely generated global dimension `≤ n`.
- `ComplexAnalytic.exists_hasFreeResolutionLE_projectiveSpaceAn`: on `ℙⁿ_an`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry ModuleCat

namespace ComplexAnalytic

/-- **The structure sheaf of a complex analytic space has locally finitely generated relations**
(Oka's theorem, in the form which passes to open subspaces). -/
theorem AnalyticSpace.hasLocalRelations (X : AnalyticSpace.{u}) :
    X.toLocallyRingedSpace.HasLocalRelations := by
  choose U n k V i f h using X.local_model
  refine LocallyRingedSpace.hasLocalRelations_of_openCover
    (fun x : X.toLocallyRingedSpace ↦ (U x).1) (fun x ↦ ⟨x, (U x).2⟩) fun x ↦ ?_
  exact LocallyRingedSpace.HasLocalRelations.hasLocalRelationsOn _
    (IsLocalModel.hasLocalRelations ⟨n x, k x, V x, i x, f x, (h x).1⟩)

/-- Finitely generated modules over a stalk of `ℂⁿ` have projective dimension `≤ n`. -/
theorem hasFGGlobalDimensionLE_stalk_complexAffineSpace (n : ℕ)
    (y : complexAffineSpace.{u} n) :
    HasFGGlobalDimensionLE ((complexAffineSpace.{u} n).presheaf.stalk y) n :=
  (LocalOkaRing.hasFGGlobalDimensionLE.{u} n).of_ringEquiv (okaStalkEquiv y).symm

/-- Bounds on the projective dimension of finitely generated modules over the stalks pass along a
morphism which is an isomorphism on the stalk. -/
theorem hasFGGlobalDimensionLE_stalk_of_isIso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (x : X) [IsIso (f.stalkMap x)] {n : ℕ}
    (h : HasFGGlobalDimensionLE (Y.presheaf.stalk (f.base x)) n) :
    HasFGGlobalDimensionLE (X.presheaf.stalk x) n :=
  h.of_ringEquiv (f.stalkMapRingEquiv x)

/-- The converse direction of `ComplexAnalytic.hasFGGlobalDimensionLE_stalk_of_isIso`. -/
theorem hasFGGlobalDimensionLE_stalk_of_isIso' {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (x : X) [IsIso (f.stalkMap x)] {n : ℕ} (h : HasFGGlobalDimensionLE (X.presheaf.stalk x) n) :
    HasFGGlobalDimensionLE (Y.presheaf.stalk (f.base x)) n :=
  h.of_ringEquiv (f.stalkMapRingEquiv x).symm

/-- **Local free resolutions on a complex analytic space** all of whose stalks have finitely
generated global dimension `≤ n` (a complex manifold of dimension `≤ n`). -/
theorem AnalyticSpace.exists_hasFreeResolutionLE (X : AnalyticSpace.{u}) {n : ℕ}
    (hdim : ∀ x : X.toLocallyRingedSpace,
      HasFGGlobalDimensionLE (X.toLocallyRingedSpace.presheaf.stalk x) n)
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (x : X.toLocallyRingedSpace) :
    ∃ (U : TopologicalSpace.Opens X.toLocallyRingedSpace) (_ : x ∈ U),
      ((X.toLocallyRingedSpace.restrictModules U).obj M).HasFreeResolutionLE n :=
  LocallyRingedSpace.exists_hasFreeResolutionLE X.hasLocalRelations hdim M x

/-- **Local free resolutions on `ℂⁿ`**: a coherent sheaf on `ℂⁿ` has, near every point, a finite
free resolution of length `≤ n`. -/
theorem exists_hasFreeResolutionLE_complexAffineSpace (n : ℕ)
    (M : SheafOfModules.{u} (complexAffineSpace.{u} n).ringSheaf) [M.IsCoherent]
    (y : complexAffineSpace.{u} n) :
    ∃ (U : TopologicalSpace.Opens (complexAffineSpace.{u} n)) (_ : y ∈ U),
      (((complexAffineSpace.{u} n).restrictModules U).obj M).HasFreeResolutionLE n :=
  LocallyRingedSpace.exists_hasFreeResolutionLE (hasLocalRelations_complexSpace _)
    (hasFGGlobalDimensionLE_stalk_complexAffineSpace n) M y

/-- **Local free resolutions on an open subset `V` of `ℂⁿ`.** -/
theorem exists_hasFreeResolutionLE_complexAffineSpace_restrict (n : ℕ)
    (V : TopologicalSpace.Opens (complexAffineSpace.{u} n))
    (M : SheafOfModules.{u} ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).ringSheaf)
    [M.IsCoherent] (y : (complexAffineSpace.{u} n).restrict V.isOpenEmbedding) :
    ∃ (U : TopologicalSpace.Opens ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding))
      (_ : y ∈ U),
      ((((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).restrictModules U).obj
        M).HasFreeResolutionLE n :=
  LocallyRingedSpace.exists_hasFreeResolutionLE ((hasLocalRelations_complexSpace _).restrict V)
    (fun z ↦ hasFGGlobalDimensionLE_stalk_of_isIso
      ((complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding) z
      (hasFGGlobalDimensionLE_stalk_complexAffineSpace n _)) M y

/-- Finitely generated modules over the stalks of `ℙⁿ_an` have projective dimension `≤ n`. -/
theorem hasFGGlobalDimensionLE_stalk_projectiveSpaceAn (n : ℕ)
    (x : (projectiveSpaceAn.{u} n).toLocallyRingedSpace) :
    HasFGGlobalDimensionLE
      ((projectiveSpaceAn.{u} n).toLocallyRingedSpace.presheaf.stalk x) n := by
  obtain ⟨i, z, rfl⟩ := projectiveSpaceAn.exists_mem_range_chart x
  exact hasFGGlobalDimensionLE_stalk_of_isIso' (projectiveSpaceAnChart.{u} i).toLRSHom z
    (hasFGGlobalDimensionLE_stalk_complexAffineSpace n z)

/-- **Local free resolutions on `ℙⁿ_an`**: a coherent sheaf on `ℙⁿ_an` has, near every point, a
finite free resolution of length `≤ n`. -/
theorem exists_hasFreeResolutionLE_projectiveSpaceAn (n : ℕ)
    (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    [M.IsCoherent] (x : (projectiveSpaceAn.{u} n).toLocallyRingedSpace) :
    ∃ (U : TopologicalSpace.Opens (projectiveSpaceAn.{u} n).toLocallyRingedSpace) (_ : x ∈ U),
      (((projectiveSpaceAn.{u} n).toLocallyRingedSpace.restrictModules U).obj
        M).HasFreeResolutionLE n :=
  (projectiveSpaceAn.{u} n).exists_hasFreeResolutionLE
    (hasFGGlobalDimensionLE_stalk_projectiveSpaceAn n) M x

end ComplexAnalytic

end
