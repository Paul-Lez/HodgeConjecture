/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.ChangeOfCoordinates

/-!
# Relabelling the variables of a germ along an embedding of index types

`LocalOkaRing.incl` (`Other/Oka/Weierstrass.lean`) reads a germ in `n` variables as a germ in `n + 1`
variables not involving the last one. Its construction uses nothing about `Fin.castSuccEmb`
beyond its being an embedding: `MvPowerSeries.LocallyConvergent.rename`, on which it rests, is
already stated for an arbitrary `e : ι ↪ κ`. This file takes the general map, `renameEmb`, and
identifies the two special cases the development already had under other names.

## Why the general map is worth having

`ComplexAnalytic.AnalyticSpace` indexes the coordinates of `ℂ^n` by `ULift (Fin n)`, so that
`ℂ^n` lives in an arbitrary universe (`Other/Oka/ComplexSpace.lean`); `Other/Oka/Weierstrass.lean` and
everything built on it indexes them by `Fin n`. A statement mentioning both an analytic space
and `LocalOkaRing.incl` therefore has to relabel `ULift (Fin n)` as `Fin n` somewhere, and
before this file there was no map to relabel it with: `LocalOkaRing.congrEquiv` relabels along a
bijection but says nothing about `incl`, and `incl` is stated only at `Fin.castSuccEmb`.

**`renameEmb` is what both of them are**, and `LocalOkaRing.congrEquiv_eq_renameEmb` and
`LocalOkaRing.incl_eq_renameEmb` say so. Once they are the same map, `renameEmb_trans` alone
proves the square that a `ULift`ed statement needs, which is
`LocalOkaRing.uliftEquiv_renameEmb` below.

## The two spellings, and why the comparison is not free

`renameEmb` is *syntactic*: it renames the variables of a power series. `congrEquiv` is
*analytic*: it is `LocalOkaRing.congr` at the linear automorphism of `ℂ^ι` permuting the
coordinates, and its value is defined by a choice of a series summing to `f ∘ φ⁻¹`. Nothing
about the definitions makes them equal, and the proof is the identity theorem: both sides sum to
`x ↦ f (x ∘ e)` near the origin, and `LocalOkaRing.congr_eq_of_represents` concludes.

## Main definitions

- `LocalOkaRing.renameEmb`: the `ℂ`-algebra map `LocalOkaRing ι →ₐ[ℂ] LocalOkaRing κ` induced by
  an embedding `ι ↪ κ` of index types, renaming the variables.
- `LocalOkaRing.uliftEquiv`: relabelling `ULift ι` as `ι`, as a `ℂ`-algebra isomorphism of germ
  rings.

## Main results

- `MvPowerSeries.Represents.renameEmb`: a series summing to `F` in the variables `ι` sums, after
  renaming along `e : ι ↪ κ`, to `x ↦ F (x ∘ e)`.
- `LocalOkaRing.renameEmb_refl` and `LocalOkaRing.renameEmb_trans`: relabelling is functorial.
- `LocalOkaRing.incl_eq_renameEmb`: **the inclusion of the Weierstrass theorems is a
  relabelling**, along `Fin.castSuccEmb`.
- `LocalOkaRing.congrEquiv_eq_renameEmb`: **the linear change of coordinates along a bijection is
  the same relabelling**, along the underlying embedding.
- `LocalOkaRing.uliftEquiv_renameEmb`: relabelling `ULift` commutes with renaming along an
  embedding, and `LocalOkaRing.uliftEquiv_renameEmb_incl`, its instance producing the inclusion
  of the Weierstrass theorems.
- `LocalOkaRing.coeff_uliftEquiv` and `LocalOkaRing.constantCoeff_uliftEquiv`: **relabelling
  `ULift` moves each coefficient to the relabelled exponent**, and fixes the constant term.

## What is not here

**`LocalOkaRing.incl` is deliberately not named in the list above**, though it is what two of the
results are stated in terms of and it is named in every paragraph before it:
`incl` is a result of `Other/Oka/Weierstrass.lean`.

**No map in the other direction.** A germ in `κ` variables restricts to one in `ι` variables
only after choosing values for the variables outside the image of `e`, which is a substitution
and not a relabelling; `Other/Oka/AnalyticSpace/ProjectionStalk.lean` records that the general
substitution does not exist in this development.

**No statement about `Other/Oka/Weierstrass.lean`'s `lastVar`.** `renameEmb e` misses exactly the
variables outside the range of `e`, and at `Fin.castSuccEmb` that is the one variable the
Weierstrass theorems distinguish; but nothing here needs the relation and `LocalOkaRing.incl`
already carries it.

**No redefinition of `LocalOkaRing.incl`.** `incl_eq_renameEmb` holds by `rfl`, so the two are
interchangeable at every goal, and moving the definition would touch `Other/Oka/Weierstrass.lean` for
no gain.
-/

@[expose] public section

open Filter Topology TopologicalSpace MvPowerSeries

universe v

namespace MvPowerSeries

variable {ι κ : Type*}

/-- **A series representing `F` represents, after renaming along an embedding `e`, the pullback
of `F` along the restriction of coordinates `x ↦ x ∘ e`.**

This is `MvPowerSeries.Represents.rename_castSucc` with `Fin.castSuccEmb` replaced by an
arbitrary embedding and `Fin.init` by `(· ∘ e)`; the proof is unchanged apart from that
substitution. The sum over the multi-indices in the image of `e` is the sum over all of them
because renaming makes the coefficients outside that image vanish. -/
lemma Represents.renameEmb (e : ι ↪ κ) [Filter.TendstoCofinite (e : ι → κ)]
    {P : MvPowerSeries ι ℂ} {F : (ι → ℂ) → ℂ} (hP : P.Represents F) :
    (rename (e : ι → κ) P).Represents (fun x ↦ F (x ∘ e)) := by
  have hcont : Continuous (fun x : κ → ℂ ↦ x ∘ (e : ι → κ)) :=
    continuous_pi fun i ↦ continuous_apply (e i)
  filter_upwards [(hcont.tendsto 0).eventually hP] with x hx
  have hinj : Function.Injective (Finsupp.mapDomain (M := ℕ) (e : ι → κ)) :=
    Finsupp.mapDomain_injective e.injective
  have hvanish : ∀ d ∉ Set.range (Finsupp.mapDomain (M := ℕ) (e : ι → κ)),
      (rename (e : ι → κ) P).term x d = 0 := fun d hd ↦ by
    rw [term, coeff_rename_eq_zero _ _ hd, zero_mul]
  refine (Function.Injective.hasSum_iff hinj hvanish).mp ?_
  have hfun : (rename (e : ι → κ) P).term x ∘ Finsupp.mapDomain (e : ι → κ) =
      P.term (x ∘ e) :=
    funext fun d ↦ term_rename e P x d
  rw [hfun]
  exact hx

end MvPowerSeries

noncomputable section

namespace LocalOkaRing

-- As in `Other/Oka/ChangeOfCoordinates.lean`, the section variables are `Fintype` rather than
-- `Finite`: the `LocalOkaRing` API is stated that way, and the `TendstoCofinite` instance the
-- rename lemmas ask for is recovered from the `Fintype` inside `renameEmb` itself.
variable {ι κ μ : Type*} [Fintype ι]

/-! ### Renaming along an embedding -/

/-- **Reading a germ in the variables `ι` as a germ in the variables `κ`, along an embedding
`e : ι ↪ κ`.**

Geometrically this is pullback along the projection `ℂ^κ → ℂ^ι`, `x ↦ x ∘ e`, which forgets the
coordinates outside the range of `e`;
`ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_coordEmb` is that reading as a theorem.
Local convergence is preserved because renaming along an embedding only reindexes the variables
(`MvPowerSeries.LocallyConvergent.rename`); the `TendstoCofinite` hypothesis that lemma asks for
is automatic here, the index types being finite. -/
def renameEmb (e : ι ↪ κ) : LocalOkaRing ι →ₐ[ℂ] LocalOkaRing κ :=
  haveI : Filter.TendstoCofinite (e : ι → κ) := Filter.tendstoCofinite_of_finite _
  ((MvPowerSeries.rename (e : ι → κ)).comp (localOkaSubring ι).val).codRestrict _
    (fun P ↦ MvPowerSeries.LocallyConvergent.rename _ P.2)

@[simp]
lemma coe_renameEmb (e : ι ↪ κ) (P : LocalOkaRing ι) :
    (renameEmb e P : MvPowerSeries κ ℂ) =
      MvPowerSeries.rename (e : ι → κ) (P : MvPowerSeries ι ℂ) :=
  rfl

/-- `renameEmb e P` sums to `x ↦ f (x ∘ e)` near the origin whenever `P` sums to `f`. -/
lemma renameEmb_represents (e : ι ↪ κ) {P : LocalOkaRing ι} {f : (ι → ℂ) → ℂ}
    (hf : (P : MvPowerSeries ι ℂ).Represents f) :
    ((renameEmb e P : LocalOkaRing κ) : MvPowerSeries κ ℂ).Represents (fun x ↦ f (x ∘ e)) := by
  haveI : Filter.TendstoCofinite (e : ι → κ) := Filter.tendstoCofinite_of_finite _
  rw [coe_renameEmb]
  exact MvPowerSeries.Represents.renameEmb e hf

/-- Relabelling along the identity does nothing. -/
@[simp]
lemma renameEmb_refl (P : LocalOkaRing ι) :
    renameEmb (Function.Embedding.refl ι) P = P :=
  Subtype.ext (by rw [coe_renameEmb]; exact MvPowerSeries.rename_id_apply _)

/-- Relabelling twice is relabelling once. -/
lemma renameEmb_trans [Fintype κ] (e : ι ↪ κ) (e' : κ ↪ μ) (P : LocalOkaRing ι) :
    renameEmb e' (renameEmb e P) = renameEmb (e.trans e') P := by
  haveI : Filter.TendstoCofinite (e : ι → κ) := Filter.tendstoCofinite_of_finite _
  haveI : Filter.TendstoCofinite (e' : κ → μ) := Filter.tendstoCofinite_of_finite _
  exact Subtype.ext (by rw [coe_renameEmb, coe_renameEmb, coe_renameEmb,
    MvPowerSeries.rename_rename]; rfl)

/-- Two embeddings that agree give the same relabelling. -/
lemma renameEmb_congr {e e' : ι ↪ κ} (h : ∀ i, e i = e' i) (P : LocalOkaRing ι) :
    renameEmb e P = renameEmb e' P := by
  rw [show e = e' from Function.Embedding.ext h]

/-! ### The two special cases the development already had -/

variable {n : ℕ}

/-- **`LocalOkaRing.incl` is the relabelling along `Fin.castSuccEmb`**, and this holds by
definition: `incl` was built from `MvPowerSeries.LocallyConvergent.rename` at that embedding,
which is what `renameEmb` is at a general one. -/
lemma incl_eq_renameEmb :
    (LocalOkaRing.incl : LocalOkaRing (Fin n) →ₐ[ℂ] LocalOkaRing (Fin (n + 1))) =
      renameEmb Fin.castSuccEmb :=
  rfl

/-- **The linear change of coordinates along a bijection of index types is the relabelling along
it.**

`congrEquiv` is defined through `LocalOkaRing.congr`, whose value at `P` is *some* locally
convergent series summing to `P.eval ∘ φ⁻¹`; `renameEmb` renames the variables. That these agree
is the identity theorem `MvPowerSeries.Represents.unique`, packaged as
`LocalOkaRing.congr_eq_of_represents`: both sides sum to `x ↦ P.eval (x ∘ e)` near the origin,
the left because `φ⁻¹` is precomposition with `e` and the right by
`LocalOkaRing.renameEmb_represents`. -/
theorem congrEquiv_eq_renameEmb [Fintype κ] (e : ι ≃ κ) (P : LocalOkaRing ι) :
    congrEquiv e P = renameEmb e.toEmbedding P := by
  refine congr_eq_of_represents (f := (P : MvPowerSeries ι ℂ).eval) P.2.represents_eval ?_
  refine (renameEmb_represents e.toEmbedding P.2.represents_eval).congr ?_
  filter_upwards with x
  rfl

/-! ### Relabelling `ULift` -/

/-- **The germ rings of `ℂ^(ULift ι)` and of `ℂ^ι` are the same ring**, relabelled.

`ComplexAnalytic.AnalyticSpace` indexes coordinates by `ULift (Fin n)` and `Other/Oka/Weierstrass.lean`
by `Fin n`; this is the isomorphism that lets a statement mention both. -/
def uliftEquiv (ι : Type*) [Fintype ι] :
    LocalOkaRing (ULift.{v} ι) ≃ₐ[ℂ] LocalOkaRing ι :=
  congrEquiv Equiv.ulift

/-- Relabelling `ULift` is a relabelling along an embedding, like everything else here. -/
lemma uliftEquiv_eq_renameEmb (P : LocalOkaRing (ULift.{v} ι)) :
    uliftEquiv ι P = renameEmb (Equiv.ulift (α := ι)).toEmbedding P :=
  congrEquiv_eq_renameEmb _ P

/-- **Relabelling `ULift` commutes with renaming along an embedding.**

`E` is any embedding of the `ULift`ed index types lying over `e`, which is what the hypothesis
`hE` says; every such `E` gives the same relabelling, by `LocalOkaRing.renameEmb_congr`, so
nothing is lost by not naming one. Both composites are the relabelling along the embedding
`ULift ι ↪ κ` sending `x` to `e x.down`, and `LocalOkaRing.renameEmb_trans` reduces each side to
it.

This is the square a `ULift`-indexed statement needs in order to reach a `Fin`-indexed one. -/
theorem uliftEquiv_renameEmb [Fintype κ] {e : ι ↪ κ} {E : ULift.{v} ι ↪ ULift.{v} κ}
    (hE : ∀ x : ULift.{v} ι, (E x).down = e x.down) (P : LocalOkaRing (ULift.{v} ι)) :
    uliftEquiv κ (renameEmb E P) = renameEmb e (uliftEquiv ι P) := by
  rw [uliftEquiv_eq_renameEmb, uliftEquiv_eq_renameEmb, renameEmb_trans, renameEmb_trans]
  exact renameEmb_congr hE P

/-- **Relabelling `ULift` moves a coefficient to the relabelled exponent**, and nothing else
happens to it.

`LocalOkaRing.uliftEquiv` is a relabelling, so the underlying series is
`MvPowerSeries.rename` of the old one and `MvPowerSeries.coeff_embDomain_rename` applies
verbatim. Stated at a general exponent rather than at `Finsupp.single` because the two consumers
below want `0` and `Finsupp.single i 1`, and `Finsupp.embDomain_single` specialises it. -/
lemma coeff_uliftEquiv (P : LocalOkaRing (ULift.{v} ι)) (d : ULift.{v} ι →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (Equiv.ulift (α := ι)).toEmbedding d)
        ((uliftEquiv ι P : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      MvPowerSeries.coeff d (P : MvPowerSeries (ULift.{v} ι) ℂ) := by
  rw [uliftEquiv_eq_renameEmb, coe_renameEmb, MvPowerSeries.coeff_embDomain_rename]

-- Not `@[simp]`: `LocalOkaRing.constantCoeff_apply` is `@[simp]` and rewrites both sides to
-- `MvPowerSeries.constantCoeff` of the coercion, so the attribute here would never fire. This is
-- the same reason `LocalOkaRing.constantCoeff_algebraMap` carries in `Other/Oka/LocalOkaRing.lean`.
/-- **Relabelling `ULift` does not move the constant term.** The exponent `0` relabels to `0`,
which is the case `d = 0` of `LocalOkaRing.coeff_uliftEquiv`. -/
lemma constantCoeff_uliftEquiv (P : LocalOkaRing (ULift.{v} ι)) :
    constantCoeff (uliftEquiv ι P) = constantCoeff P := by
  rw [constantCoeff_apply, constantCoeff_apply,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ι →₀ ℕ) = Finsupp.embDomain (Equiv.ulift (α := ι)).toEmbedding 0 by simp]
  exact coeff_uliftEquiv P 0

/-- **The instance of the square that produces `LocalOkaRing.incl`**: an embedding of
`ULift (Fin n)` into `ULift (Fin (n + 1))` lying over `Fin.castSucc` becomes, after relabelling
both germ rings, the inclusion of the Weierstrass theorems. -/
theorem uliftEquiv_renameEmb_incl {E : ULift.{v} (Fin n) ↪ ULift.{v} (Fin (n + 1))}
    (hE : ∀ x : ULift.{v} (Fin n), (E x).down = x.down.castSucc)
    (P : LocalOkaRing (ULift.{v} (Fin n))) :
    uliftEquiv (Fin (n + 1)) (renameEmb E P) = LocalOkaRing.incl (uliftEquiv (Fin n) P) := by
  rw [incl_eq_renameEmb]
  exact uliftEquiv_renameEmb hE P

end LocalOkaRing

end

end
