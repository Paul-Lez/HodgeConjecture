/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Basic
public import Other.Oka.Noetherian
public import Other.Oka.StalkEquiv

/-!
# The local rings of a complex analytic space are Noetherian

The stalks of the structure sheaf of a complex analytic space are Noetherian local rings. This
is the standing hypothesis behind local analytic geometry, and the companion statement to
`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf` of `Other/Oka/AnalyticSpace/Coherent.lean`.

The deduction is short, because the two inputs are already available. On `ℂ^ι` the stalk at a
point is the ring of convergent power series at the origin (`okaStalkEquiv` of
`Other/Oka/StalkEquiv.lean`), which is Noetherian by the Rückert basis theorem
(`LocalOkaRing.instIsNoetherianRing` of `Other/Oka/Noetherian.lean`). Restricting to an open subset
does not change the stalks, and a local model has, by definition, surjective stalk maps from an
open subset of some `ℂ^n`, so its stalks are quotients of Noetherian rings. An analytic space is
locally a local model, and again restricting to an open subset does not change the stalks.

## Main results

- `isNoetherianRing_okaStalk` and `isNoetherianRing_stalk_complexSpace`: the stalks of
  `𝒪_{ℂ^ι}` are Noetherian.
- `ComplexAnalytic.IsLocalModel.isNoetherianRing_stalk`: the stalks of a local model are
  Noetherian.
- `ComplexAnalytic.AnalyticSpace.instIsNoetherianRingStalk`: the stalks of a complex analytic
  space are Noetherian; with `AlgebraicGeometry.LocallyRingedSpace.isLocalRing` they are
  therefore Noetherian local rings.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
- [Hans Grauert and Reinhold Remmert, *Theory of Stein spaces*][grauert-remmert1979], Chapter II
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

/-- **The stalks of the structure sheaf of `ℂ^ι` are Noetherian**: the stalk at `y` is the ring
of power series converging near the origin (`okaStalkEquiv`), which is Noetherian by the
Rückert basis theorem (`LocalOkaRing.instIsNoetherianRing`). -/
instance isNoetherianRing_okaStalk (ι : Type u) [Fintype ι] (y : ι → ℂ) :
    IsNoetherianRing ((okaCommPresheaf ι).stalk y) :=
  isNoetherianRing_of_ringEquiv (LocalOkaRing ι) (okaStalkEquiv y).symm

/-- The stalks of `ℂ^ι` as a locally ringed space are Noetherian.

This restates `isNoetherianRing_okaStalk` for `complexSpace ι`. Both forms are needed as
instances: `(complexSpace ι).presheaf` is definitionally `okaCommPresheaf ι`, but instance
search does not unfold the definition of `complexSpace`. -/
instance isNoetherianRing_stalk_complexSpace (ι : Type u) [Fintype ι] (y : ι → ℂ) :
    IsNoetherianRing ((complexSpace ι).presheaf.stalk y) :=
  isNoetherianRing_okaStalk ι y

namespace ComplexAnalytic

/-- Restricting a locally ringed space to an open subspace does not change its stalks, so
Noetherianity of the stalks is inherited. -/
theorem isNoetherianRing_stalk_restrict {X : LocallyRingedSpace.{u}} {U : TopCat.{u}}
    {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) (x : U)
    (hX : IsNoetherianRing (X.presheaf.stalk (f x))) :
    IsNoetherianRing ((X.restrict h).presheaf.stalk x) :=
  isNoetherianRing_of_ringEquiv _
    (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv

/-- The stalks of a local model are Noetherian: they are quotients of the stalks of an open
subspace of some `ℂ^n`. -/
theorem IsLocalModel.isNoetherianRing_stalk {M : LocallyRingedSpace.{u}} (hM : IsLocalModel M)
    (x : M) : IsNoetherianRing (M.presheaf.stalk x) := by
  obtain ⟨n, k, U, i, f, hcut⟩ := hM
  have hY : IsNoetherianRing
      (((complexAffineSpace.{u} n).restrict U.isOpenEmbedding).presheaf.stalk (i.base x)) :=
    isNoetherianRing_stalk_restrict _ _ inferInstance
  exact isNoetherianRing_of_surjective _ _ (i.stalkMap x).hom (hcut.surjective_stalkMap x)

namespace AnalyticSpace

/-- **The local rings of a complex analytic space are Noetherian.**

Every point has a neighbourhood which is a local model, whose stalks are Noetherian, and
restricting to an open subspace does not change the stalk. Together with the local ring
structure carried by any `LocallyRingedSpace` this says that the local rings of a complex
analytic space are Noetherian local rings. As with coherence, the `ℂ`-algebra structure plays
no role: this is a statement about the underlying locally ringed space. -/
instance instIsNoetherianRingStalk (X : AnalyticSpace.{u}) (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨U, n, k, V, i, f, hcut, -⟩ := X.local_model x
  have hM : IsNoetherianRing
      ((X.toLocallyRingedSpace.restrict U.1.isOpenEmbedding).presheaf.stalk ⟨x, U.2⟩) :=
    IsLocalModel.isNoetherianRing_stalk ⟨n, k, V, i, f, hcut⟩ ⟨x, U.2⟩
  exact isNoetherianRing_of_ringEquiv _
    (X.toLocallyRingedSpace.restrictStalkIso U.1.isOpenEmbedding ⟨x, U.2⟩).commRingCatIsoToRingEquiv

end AnalyticSpace

end ComplexAnalytic

end
