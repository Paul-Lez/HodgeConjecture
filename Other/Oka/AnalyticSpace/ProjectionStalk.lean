/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.HolomorphicMap
public import Other.Oka.RenameIndex

/-!
# Forgetting coordinates, on germs and stalks

An embedding `e : κ ↪ ι` of index types gives the map `ℂ^ι → ℂ^κ` forgetting the coordinates
outside its range, and that map is `ComplexAnalytic.okaMapHom` at the family of coordinate
functions `fun j ↦ coord (e j)`. This file computes what it does to a germ: **through
`okaStalkEquiv`, it is `LocalOkaRing.renameEmb e`**, the relabelling of the variables.

At `e = Fin.castSuccEmb` that is the projection `ℂ^(n+1) → ℂ^n` and the relabelling is
`LocalOkaRing.incl`, the inclusion of the power series that do not involve the last variable.
That identification is what a quotient statement about `LocalOkaRing` needs before it can be read
as a statement about a morphism of spaces. `LocalOkaRing.quotientDegreeOneEquiv` and
`LocalOkaRing.quotientSimpleZeroEquiv` (`Other/Oka/Regular.lean`) are both built from
`LocalOkaRing.incl` followed by a quotient map, and without a lemma naming the geometric map that
`incl` comes from they identify the germ ring one dimension down with a quotient by an
*abstract* isomorphism rather than by the stalk map of the projection.

## The proof, in one sentence

The Taylor expansion of `s ∘ (· ∘ e)` at `z` is the Taylor expansion of `s` at `z ∘ e` with the
variables renamed. `MvPowerSeries.Represents.renameEmb` is that sentence about power series,
`OkaRing.germ_eq_of_represents` is what reduces a claim about a germ to a claim about what its
series represents, and `LocalOkaRing.coe_renameEmb` says the rename is `renameEmb`.

**Why the equality below is taken on a neighbourhood, which is a fact about the rewrite and not
about the claim.** `OkaRing.toGlobalFun` is total ; it is `Function.extend Subtype.val _ 0` ; so
off the preimage of `W` both sides are `0`, and `(w + z) ∘ e ∈ W` is the same condition on
either side. The identity therefore holds **globally**; what the neighbourhood buys is the
membership hypothesis that `OkaRing.toGlobalFun_apply` asks for. Dropping it is possible and
costs a `by_cases` and two `Function.extend_apply'` rewrites ; four lines longer, and four lines
that say nothing about the geometry. **The obstacle is real and it is the rewrite**: with a
global `filter_upwards` both rewrites fail, on a hypothesis that says only `w ∈ Set.univ`.

## The two indexings, and why the last section is not an isomorphism of spaces

`ComplexAnalytic.AnalyticSpace` indexes the coordinates of `ℂ^n` by `ULift (Fin n)`, so that the
underlying type lives in an arbitrary universe; `Other/Oka/Weierstrass.lean` and `LocalOkaRing.incl`
index them by `Fin n`. **What does not exist is a comparison of the two as spaces that survives
into an arbitrary universe**, and that is the only kind `AnalyticSpace` has a use for: the
`ULift` is carried for no other reason than to keep `complexAffineSpace` polymorphic, as
`Other/Oka/ComplexSpace.lean` says where it is defined. For `u > 0` there is not even a type to write
down: `complexSpace (Fin n)` is a `LocallyRingedSpace.{0}` while the space underlying
`AnalyticSpace.complexAffineSpace.{u} n` is a `LocallyRingedSpace.{u}`, so the two are objects of
two different categories and the arrow between them does not elaborate.

**At `u = 0` it does, and morphisms exist in both directions**, out of this file's own API:
`ComplexAnalytic.coordEmb` at the embedding underlying `Equiv.ulift` and at the one underlying
`Equiv.ulift.symm`, each fed to `ComplexAnalytic.okaMapHom`, whose two underlying maps
`ComplexAnalytic.okaMapFun_coordEmb` makes mutually inverse in three lines. Nothing below uses
that, **because it does not generalise**: `ComplexAnalytic.okaMapHom`
(`Other/Oka/AnalyticSpace/HolomorphicMap.lean`) binds its two index types to one universe, and
`ULift (Fin n)` shares a universe with `Fin n` at `u = 0` and nowhere else.
So a reader who goes looking for an isomorphism between the two spellings of `ℂ^n` should read
this as the answer ; not that the question cannot be asked, but that the only place it can be
answered is `Type 0`, which is the one place `AnalyticSpace` was built not to be confined to.

What can be compared in every universe is the germ rings, which are rings and not spaces:
`LocalOkaRing.uliftEquiv` relabels `ULift ι` as `ι`, and `LocalOkaRing.uliftEquiv_renameEmb_incl`
says the relabelling turns the `ULift`ed `Fin.castSucc` into `incl`. The last section below is
that bridge crossed once.

## Main definitions

- `ComplexAnalytic.coordEmb`: the coordinates of `ℂ^ι` indexed by an embedded `κ`, whose
  `ComplexAnalytic.okaMapHom` is the map forgetting the rest, and `ComplexAnalytic.projCoords`,
  its instance at `Fin.castSuccEmb`.
- `ComplexAnalytic.uliftCastSuccEmb`: `Fin.castSucc` relabelled through `ULift`, and
  `ComplexAnalytic.AnalyticSpace.proj`, the projection `ℂ^(n+1) ⟶ ℂ^n` of complex analytic
  spaces it gives.

## Main results

- `ComplexAnalytic.okaMapFun_coordEmb`: the underlying map of the projection along `e` is
  `(· ∘ e)`, and `ComplexAnalytic.okaMapFun_projCoords`, its instance at `Fin.castSuccEmb`.
- `ComplexAnalytic.germ_okaMapC_coordEmb`: the germ of a pullback at `z` is the germ at `z ∘ e`
  with the variables relabelled, and `ComplexAnalytic.germ_okaMapC_projCoords`.
- `ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_coordEmb`: **the stalk map of the projection
  is that relabelling**, transported along the Taylor-expansion isomorphism, and
  `ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords`.
- `ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj`: **the stalk map of the
  projection `ℂ^(n+1) ⟶ ℂ^n` of complex analytic spaces is the inclusion of the Weierstrass
  theorems**, after both germ rings are relabelled from `ULift (Fin _)` to `Fin _`.
- `ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply` and
  `ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply`: the last two at an
  arbitrary element of the stalk rather than at a germ.

## What is not here

**Neither `LocalOkaRing.incl` nor `LocalOkaRing.renameEmb` nor `okaStalkEquiv` is named in the
list above**, though all three are what the results are stated in terms of and all three are
named in the paragraphs before it. That is deliberate: none of them is a result of this file.

**No `IsIso`.** Assembling this with `ComplexAnalytic.IsCutOutBy`'s `surjective_stalkMap` and
`ker_stalkMap` into an isomorphism of stalks for a hypersurface with a simple zero is
`Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` and not here. That file is *about* the projection ; it is
in its title and in four of the six declarations it advertises ; and what it takes from this one
is of two kinds: the two `…_apply` results, which are the only **theorems** of this file its
proofs use, and three **definitions**, `ComplexAnalytic.projCoords`, `ComplexAnalytic.coordEmb`
and `ComplexAnalytic.uliftCastSuccEmb`, which its two headline theorems are stated at and could
not be stated without. The other statement of that shape in the repository is
`ComplexAnalytic.isIso_stalkMap_okaMapHom`
(`Other/Oka/AnalyticSpace/StalkLocalInverse.lean`), whose hypothesis is an analytic local inverse
rather than a cut-out.

**No general substitution.** The Taylor series of `s ∘ okaMapFun u` for an arbitrary family `u`
is a composition of power series, which this repository does not have. Forgetting coordinates is
exactly the case where the operation already exists under another name,
`LocalOkaRing.renameEmb`.

**No section of the projection.** A germ in `ι` variables does not restrict to one in `κ`
variables without choosing values for the coordinates outside the range of `e`, which is again a
substitution; `Other/Oka/RenameIndex.lean` records the same absence one level down.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

noncomputable section

namespace ComplexAnalytic

universe u

variable {n : ℕ}

/-! ### Forgetting the coordinates outside an embedding -/

section CoordEmb

variable {ι κ : Type u} [Fintype ι]

/-- **The coordinates of `ℂ^ι` indexed by an embedded `κ`, as global sections of its structure
sheaf.**

`ComplexAnalytic.okaMapHom` at this family is the map `ℂ^ι → ℂ^κ` forgetting the coordinates
outside the range of `e`; `ComplexAnalytic.okaMapFun_coordEmb` says so. -/
def coordEmb (e : κ ↪ ι) : κ → OkaRing (⊤ : Opens (ι → ℂ)) :=
  fun j ↦ coord (e j)

/-- **The map underlying the projection along `e` is restriction of coordinates.** -/
theorem okaMapFun_coordEmb (e : κ ↪ ι) (z : ι → ℂ) :
    okaMapFun (coordEmb e) z = z ∘ e := by
  funext j
  rw [okaMapFun_apply, coordEmb, evalHom_coord]
  rfl

/-- **The germ of `s ∘ (· ∘ e)` at `z` is `LocalOkaRing.renameEmb e` of the germ of `s` at
`z ∘ e`.**

`OkaRing.germ_eq_of_represents` reduces this to what the two power series represent, and
`LocalOkaRing.renameEmb_represents` is the statement that a series representing `F` in the
variables `κ` represents `F ∘ (· ∘ e)` in the variables `ι`. The only computation is
`(w + z) ∘ e = w ∘ e + z ∘ e`, which holds by definition.

The `filter_upwards` takes the preimage of `W` translated to the origin because
`OkaRing.toGlobalFun_apply` wants a membership hypothesis, **not because the identity fails off
it**: `OkaRing.toGlobalFun` extends by zero, so both sides vanish there. See the module
docstring. -/
theorem germ_okaMapC_coordEmb [Fintype κ] {e : κ ↪ ι} {z : ι → ℂ} {W : Opens (κ → ℂ)}
    (hz : z ∈ (Opens.map (okaMapBase (coordEmb e))).obj W) (s : OkaRing W) :
    OkaRing.germ hz (okaMapC (coordEmb e) W s)
      = LocalOkaRing.renameEmb e
          (OkaRing.germ (show okaMapFun (coordEmb e) z ∈ W from hz) s) := by
  refine OkaRing.germ_eq_of_represents _ ?_
  refine (LocalOkaRing.renameEmb_represents e
    (OkaRing.germ_represents (show okaMapFun (coordEmb e) z ∈ W from hz) s)).congr ?_
  have hset : IsOpen {w : ι → ℂ |
      w + z ∈ (Opens.map (okaMapBase (coordEmb e))).obj W} :=
    ((Opens.map (okaMapBase (coordEmb e))).obj W).isOpen.preimage (by fun_prop)
  filter_upwards [hset.mem_nhds (by simpa using hz)] with w hw
  have hkey : w ∘ e + okaMapFun (coordEmb e) z = okaMapFun (coordEmb e) (w + z) := by
    rw [okaMapFun_coordEmb, okaMapFun_coordEmb]
    rfl
  have hw' : okaMapFun (coordEmb e) (w + z) ∈ W := hw
  rw [hkey, s.toGlobalFun_apply hw', OkaRing.toGlobalFun_apply _ hw]
  rfl

/-- **Transported along `okaStalkEquiv`, the stalk map of the projection along `e` is
`LocalOkaRing.renameEmb e`.**

This is the previous statement at the spelling a caller holding a stalk rather than a germ needs:
`PresheafedSpace.stalkMap_germ_apply` turns the stalk map on a germ into the germ of the pullback,
and `okaStalkEquiv_germ` is the Taylor expansion at either end. Stated on germs because every
element of the stalk is one ; `TopCat.Presheaf.exists_germ_eq` ; so this determines the stalk map
completely. -/
theorem okaStalkEquiv_stalkMap_okaMapHom_coordEmb [Fintype κ] {e : κ ↪ ι} {z : ι → ℂ}
    {W : Opens (κ → ℂ)} (hw : okaMapFun (coordEmb e) z ∈ W) (s : OkaRing W) :
    okaStalkEquiv z ((okaMapHom (coordEmb e)).stalkMap z
        ((okaCommPresheaf κ).germ W _ hw s))
      = LocalOkaRing.renameEmb e (okaStalkEquiv (okaMapFun (coordEmb e) z)
          ((okaCommPresheaf κ).germ W _ hw s)) := by
  have hz : z ∈ (Opens.map (okaMapBase (coordEmb e))).obj W := hw
  have hmap : ((okaMapPre (coordEmb e)).stalkMap z).hom
        ((okaCommPresheaf κ).germ W ((okaMapPre (coordEmb e)).base z) hw s) =
      (okaCommPresheaf ι).germ ((Opens.map (okaMapBase (coordEmb e))).obj W) z hz
        (okaMapC (coordEmb e) W s) :=
    PresheafedSpace.stalkMap_germ_apply (okaMapPre (coordEmb e)) W z hw s
  rw [show (okaMapHom (coordEmb e)).stalkMap z
      ((okaCommPresheaf κ).germ W _ hw s) = _ from hmap,
    okaStalkEquiv_germ, okaStalkEquiv_germ, germ_okaMapC_coordEmb]

end CoordEmb

/-! ### The projection `ℂ^(n+1) → ℂ^n` -/

/-- **The first `n` coordinates of `ℂ^(n+1)`, as global sections of its structure sheaf.**

`ComplexAnalytic.okaMapHom` at this family is the projection forgetting the last coordinate;
`ComplexAnalytic.okaMapFun_projCoords` says so. It is `ComplexAnalytic.coordEmb` at
`Fin.castSuccEmb`, and `ComplexAnalytic.projCoords_eq_coordEmb` says so by `rfl`. -/
def projCoords (n : ℕ) : Fin n → OkaRing (⊤ : Opens (Fin (n + 1) → ℂ)) :=
  coordEmb (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))

/-- The projection is the case `e = Fin.castSuccEmb` of forgetting coordinates. -/
theorem projCoords_eq_coordEmb (n : ℕ) :
    projCoords n = coordEmb (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) :=
  rfl

/-- **The map underlying the projection is `Fin.init`.** -/
theorem okaMapFun_projCoords (z : Fin (n + 1) → ℂ) :
    okaMapFun (projCoords n) z = Fin.init z :=
  okaMapFun_coordEmb (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) z

/-- **The germ of `s ∘ proj` at `z` is `LocalOkaRing.incl` of the germ of `s` at `proj z`.**

`ComplexAnalytic.germ_okaMapC_coordEmb` at `Fin.castSuccEmb`, using that
`LocalOkaRing.incl` is `LocalOkaRing.renameEmb` there (`LocalOkaRing.incl_eq_renameEmb`). -/
theorem germ_okaMapC_projCoords {z : Fin (n + 1) → ℂ} {W : Opens (Fin n → ℂ)}
    (hz : z ∈ (Opens.map (okaMapBase (projCoords n))).obj W) (s : OkaRing W) :
    OkaRing.germ hz (okaMapC (projCoords n) W s)
      = LocalOkaRing.incl (OkaRing.germ (show okaMapFun (projCoords n) z ∈ W from hz) s) :=
  germ_okaMapC_coordEmb (e := (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))) hz s

/-- **Transported along `okaStalkEquiv`, the stalk map of the projection is
`LocalOkaRing.incl`.**

`ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_coordEmb` at `Fin.castSuccEmb`. Stated on germs
because every element of the stalk is one ; `TopCat.Presheaf.exists_germ_eq` ; so this determines
the stalk map completely. -/
theorem okaStalkEquiv_stalkMap_okaMapHom_projCoords {z : Fin (n + 1) → ℂ}
    {W : Opens (Fin n → ℂ)} (hw : okaMapFun (projCoords n) z ∈ W) (s : OkaRing W) :
    okaStalkEquiv z ((okaMapHom (projCoords n)).stalkMap z
        ((okaCommPresheaf (Fin n)).germ W _ hw s))
      = LocalOkaRing.incl (okaStalkEquiv (okaMapFun (projCoords n) z)
          ((okaCommPresheaf (Fin n)).germ W _ hw s)) :=
  okaStalkEquiv_stalkMap_okaMapHom_coordEmb (e := (Fin.castSuccEmb : Fin n ↪ Fin (n + 1))) hw s

/-- **The previous statement at an arbitrary element of the stalk** rather than at a germ.

The germ form determines the stalk map, since every element of the stalk is a germ; this is that
sentence carried out, and it is what a consumer holding an opaque element of the stalk ; anything
produced by surjectivity of another stalk map, say ; actually needs.
`Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` is the first such consumer. -/
theorem okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply {z : Fin (n + 1) → ℂ}
    (t : (okaCommPresheaf (Fin n)).stalk (okaMapFun (projCoords n) z)) :
    okaStalkEquiv z ((okaMapHom (projCoords n)).stalkMap z t) =
      LocalOkaRing.incl (okaStalkEquiv (okaMapFun (projCoords n) z) t) := by
  obtain ⟨W, hw, s, rfl⟩ := (okaCommPresheaf (Fin n)).exists_germ_eq t
  exact okaStalkEquiv_stalkMap_okaMapHom_projCoords hw s

/-! ### The same projection between complex analytic spaces

`ComplexAnalytic.AnalyticSpace.complexAffineSpace n` indexes its coordinates by
`ULift (Fin n)`, so the projection between two of them is `coordEmb` at an embedding of `ULift`ed
index types and its stalk map is the relabelling along that embedding. Crossing to
`LocalOkaRing.incl`, which is stated for `Fin`, is `LocalOkaRing.uliftEquiv_renameEmb_incl`. -/

section Ulift

variable {n : ℕ}

/-- **`Fin.castSucc`, relabelled through `ULift`**: the embedding of index types underlying the
projection `ℂ^(n+1) ⟶ ℂ^n` of complex analytic spaces. -/
def uliftCastSuccEmb (n : ℕ) : ULift.{u} (Fin n) ↪ ULift.{u} (Fin (n + 1)) where
  toFun j := ULift.up j.down.castSucc
  inj' _ _ h := ULift.ext _ _ (Fin.castSucc_injective n (ULift.up.inj h))

/-- **The projection `ℂ^(n+1) ⟶ ℂ^n` forgetting the last coordinate, as a morphism of complex
analytic spaces.** -/
def AnalyticSpace.proj (n : ℕ) :
    AnalyticSpace.complexAffineSpace.{u} (n + 1) ⟶ AnalyticSpace.complexAffineSpace.{u} n :=
  AnalyticSpace.okaMap (coordEmb (uliftCastSuccEmb.{u} n))

/-- The morphism of locally ringed spaces underlying `ComplexAnalytic.AnalyticSpace.proj`. -/
theorem AnalyticSpace.toLRSHom_proj (n : ℕ) :
    (AnalyticSpace.proj.{u} n).toLRSHom = okaMapHom (coordEmb (uliftCastSuccEmb.{u} n)) :=
  rfl

/-- **The stalk map of the projection `ℂ^(n+1) ⟶ ℂ^n` of complex analytic spaces is
`LocalOkaRing.incl`**, once both germ rings are relabelled from `ULift (Fin _)` to `Fin _`.

This is `ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_coordEmb` at
`ComplexAnalytic.uliftCastSuccEmb`, followed by `LocalOkaRing.uliftEquiv_renameEmb_incl` to cross
from the indexing an analytic space uses to the one the Weierstrass theorems use. The relabelling
is unavoidable and is not an isomorphism of spaces; see the module docstring. -/
theorem AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj
    {z : ULift.{u} (Fin (n + 1)) → ℂ} {W : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)}
    (hw : okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) z ∈ W) (s : OkaRing W) :
    LocalOkaRing.uliftEquiv (Fin (n + 1))
        (okaStalkEquiv z ((AnalyticSpace.proj.{u} n).toLRSHom.stalkMap z
          ((okaCommPresheaf (ULift.{u} (Fin n))).germ W _ hw s)))
      = LocalOkaRing.incl (LocalOkaRing.uliftEquiv (Fin n)
          (okaStalkEquiv (okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) z)
            ((okaCommPresheaf (ULift.{u} (Fin n))).germ W _ hw s))) := by
  have h := okaStalkEquiv_stalkMap_okaMapHom_coordEmb (e := uliftCastSuccEmb.{u} n) hw s
  exact (congrArg (fun x ↦ LocalOkaRing.uliftEquiv (Fin (n + 1)) x) h).trans
    (LocalOkaRing.uliftEquiv_renameEmb_incl (fun _ ↦ rfl) _)

/-- **The previous statement at an arbitrary element of the stalk** rather than at a germ, as
`ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply` is for the `Fin` indexing.

Stated on `ComplexAnalytic.okaMapHom` rather than on
`ComplexAnalytic.AnalyticSpace.proj`, which is `ComplexAnalytic.AnalyticSpace.toLRSHom_proj`
away, because the consumer holds a morphism of locally ringed spaces. -/
theorem AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply
    {z : ULift.{u} (Fin (n + 1)) → ℂ}
    (t : (okaCommPresheaf (ULift.{u} (Fin n))).stalk
      (okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) z)) :
    LocalOkaRing.uliftEquiv (Fin (n + 1)) (okaStalkEquiv z
        ((okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap z t)) =
      LocalOkaRing.incl (LocalOkaRing.uliftEquiv (Fin n)
        (okaStalkEquiv (okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) z) t)) := by
  obtain ⟨W, hw, s, rfl⟩ := (okaCommPresheaf (ULift.{u} (Fin n))).exists_germ_eq t
  exact AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj hw s

end Ulift

end ComplexAnalytic

end

end
