/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.StandardEtaleLocalIso
public import Other.Oka.AnalyticSpace.CutOutCancel
public import Other.Oka.AnalyticSpace.CutOutLocalIso

/-!
# A standard étale morphism over a **presented** base analytifies to a local isomorphism

`Other/Oka/Analytification/StandardEtaleLocalIso.lean` proves this over `ℂ^n` ; that is, at `k = 0`,
where the whole of that file sits under one `variable` line. This file proves it over an
arbitrary presented base, at every `k`:

    ComplexAnalytic.AnalyticSpace.IsLocalIso (analytificationMap (etalePresHom g F G))

with **no** `ComplexAnalytic.analytificationInclHom g` after it. The target is the base's own
analytification `X^an` and not `ℂ^n`, and that distinction is the whole reason this is a theorem
rather than the false statement `Other/Oka/Analytification/StandardEtaleLocalIso.lean` records: the
composite *followed by* the inclusion into `ℂ^n` fails at `k ≥ 1` for every `g` whose zero locus
is a proper non-empty closed subset, because a local isomorphism has open image and a proper
closed zero locus has empty interior. **Openness in `X^an` is not openness in `ℂ^n`**, so nothing
in that argument touches the statement above.

**That failure is a theorem since 2026-09-02** ;
`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`
(`Other/Oka/Analytification/StandardEtaleNotLocalIso.lean`), which takes *proper* as `∃ j, g j ≠ 0` and
*non-empty* as a `Nonempty` on the source ; so the contrast this paragraph draws is now between
two compiled statements rather than between a theorem and an argument.

## No implicit function theorem *relative to `X^an`*, and the files that priced one

Five sites said that a statement over a general base *"needs an implicit function theorem relative
to `X^an`, which `Other/Oka/Analysis/Calculus/Implicit.lean` does not have"*. They stood, at the tree
this section was written against, in **four** files, and four of them in these three:

* `Other/Oka/AnalyticSpace/SimpleZeroPolynomial.lean`;
* `Other/Oka/Analytification/StandardEtaleAnalytification.lean`, **twice** ; the full price in one
  place and the same price in a shorter wording in another, which is the whole of why four sites
  sit in three files;
* `Other/Oka/Analytification/StandardEtaleLocalIso.lean`.

The five are about the projection to `ℂ^n`, which is a different statement and is the false one;
the sentence was never tested against this one. **The step from `k = 0` to `k ≥ 1` takes no
analysis at all**: the
`k ≥ 1` configuration is the `k = 0` one restricted over a subspace on both sides, and the
transport of local isomorphisms across such a restriction is
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ`
(`Other/Oka/AnalyticSpace/CutOutLocalIso.lean`), which is a statement about cut-out data and mentions
no polynomial.

**What this file does *not* claim is that no implicit function theorem is spent anywhere beneath
it**, and the claim would be false. Step 3 below is
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`
(`Other/Oka/AnalyticSpace/SimpleZeroTopology.lean`), whose topological half runs through
`isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter` in `Other/Oka/Analysis/Calculus/Implicit.lean`
; that file imports it, and its own docstring calls that lemma *"the implicit function theorem"*
in terms. **One is spent, relative to `ℂ^n`, and it is the one the `k = 0` line already spent.**
The sharp claim is that going to a presented base costs no second one relative to `X^an`, which
is what the five sites priced and what nothing here needs.

## The route, in the order the declarations come

Write `W₀` for the hypersurface `{F = 0} ⊆ ℂ^(n+1)` ; `ComplexAnalytic.hypersurfaceOnly`, which
is `ComplexAnalytic.hypersurfacePresentation` over the **empty** base ; and `W` for the `k ≥ 1`
hypersurface `ComplexAnalytic.hypersurfacePresentation g F`.

1. **`W` sits inside `W₀`.** The ideal of `W₀` is contained in that of `W`
   (`ComplexAnalytic.presentationIdeal_hypersurfaceOnly_le`), so
   `ComplexAnalytic.analytificationCompare` gives `ComplexAnalytic.hypersurfaceCompare`, a
   morphism `W^an ⟶ W₀^an` over `ℂ^(n+1)`
   (`ComplexAnalytic.hypersurfaceCompare_comp`).
2. **And it is cut out inside it by the relations of the base, read one variable up.** That is
   `ComplexAnalytic.isCutOutBy_hypersurfaceCompare`, and it is
   `ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq` ; the cancellation lemma ; at the two data
   `ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface` and
   `ComplexAnalytic.isCutOutBy_analytificationInclHom`, whose families differ exactly by
   `ComplexAnalytic.polyPresentation`.
3. **The open to take is `D(G · ∂F)` and not `D(G)`**, and only on the `W₀` side. On `W₀` the
   derivative hypothesis of
   `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` is not available on `D(G)` ;
   `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces the derivative only at points of `W`,
   which is a proper closed subset of `W₀` ; so it is asked on `D(G · ∂F)`, where it holds by
   construction. `ComplexAnalytic.isLocalIso_hypersurfaceOnly_ofRestrict_comp_proj` is that, and
   it asks **nothing of `g`**.
4. **On the `W` side the two opens are the same open.**
   `ComplexAnalytic.localisationOpen_mul_pderiv` says `D(G · ∂F) = D(G)` *in `W^an`*, because
   `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` makes the derivative invertible wherever `G` is.
   **This is what reconciles the two sides**, and it is why nothing here has to compare two
   different open subspaces: one formula, `G · ∂F`, names both, and on `W` it names `D(G)` too.
5. **Then the transport.** `ComplexAnalytic.isLocalIso_ofRestrict_comp_analytificationMap` is
   `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ` at `p` the projection of
   step 3, `iX` the base's inclusion into `ℂ^n`, `iY` the restriction of step 2 and `q` the map
   this file is about; its square
   (`ComplexAnalytic.ofRestrict_comp_analytificationMap_comp_analytificationInclHom`) is
   `ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp` and step 1 read together.
6. **And the identification.** `ComplexAnalytic.etaleAnalytificationIso_hom_comp` ; an equation
   already in the tree, general in `k` ; replaces the étale analytification by `D(G)` in `W^an`
   over the base, and `ComplexAnalytic.AnalyticSpace.isLocalIso_comp` closes it.

## Main definitions

- `ComplexAnalytic.hypersurfaceOnly`: the hypersurface of `F` alone in `ℂ^(n+1)`, as a
  presentation with one relation.
- `ComplexAnalytic.hypersurfaceCompare`: the inclusion of the `k ≥ 1` hypersurface into it.

## Main results

- `ComplexAnalytic.presentationIdeal_hypersurfaceOnly_le`: the ideal of `{F = 0}` is contained in
  the ideal of the `k ≥ 1` hypersurface.
- `ComplexAnalytic.hypersurfaceCompare_comp`: **the comparison is a morphism over `ℂ^(n+1)`.**
- `ComplexAnalytic.range_section_hypersurfacePresentation`: the sections cutting out the `k ≥ 1`
  hypersurface are, as a set, the single section cutting out `{F = 0}` together with the relations
  of the base read one variable up.
- `ComplexAnalytic.isCutOutBy_hypersurfaceCompare`: **the `k ≥ 1` hypersurface is cut out inside
  `{F = 0}` by the pullbacks of the relations of the base** ; the cancellation, at these
  arguments.
- `ComplexAnalytic.pullbackΓ_proj_ofMvPolynomial`: **pulling a polynomial back along the
  projection `ℂ^(n+1) ⟶ ℂ^n` is reading it one variable up.**
- `ComplexAnalytic.isLocalIso_hypersurfaceOnly_ofRestrict_comp_proj`: **`D(G · ∂F)` inside
  `{F = 0}` projects to `ℂ^n` as a local isomorphism**, for every `g`.
- `ComplexAnalytic.localisationOpen_mul_pderiv`: **inverting the derivative as well changes
  nothing on the `k ≥ 1` hypersurface** ; the two opens are one open.
- `ComplexAnalytic.restrictSections_hypersurfaceCompare`: the family cutting out the restriction
  is the pullback of the relations of the base along that projection.
- `ComplexAnalytic.ofRestrict_comp_analytificationMap_comp_analytificationInclHom`: the square
  the transport consumes.
- `ComplexAnalytic.isLocalIso_ofRestrict_comp_analytificationMap`: **`D(G · ∂F)` inside the
  `k ≥ 1` hypersurface maps to the base's analytification as a local isomorphism.**
- `ComplexAnalytic.comap_localisationOpen_hypersurfaceCompare`: **that open is `D(G)`** ; the
  comparison's preimage of `D(G · ∂F)`, with the derivative deleted by the theorem above.
- `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`: **the analytification of a
  standard étale morphism over a presented base is a local isomorphism onto that base**, at every
  `k`.

## What is not here

* **No `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`.** Unrestricted finiteness at `k ≥ 1` is
  false ; `Other/Oka/Analytification/MonicHypersurface.lean` carries the counterexample ; and over an
  open subset of the base it is `Other/Oka/Analytification/StandardEtaleFinitenessBase.lean`'s, at every
  `k`, with `Other/Oka/Analytification/StandardEtaleFiniteness.lean`'s the `k = 0` statement about the
  composite to `ℂ^n` instead. The local-isomorphism field is what this file supplies and it is
  only one of the two; the two together are
  `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom`
  (`Other/Oka/Analytification/StandardEtaleFiniteEtaleBase.lean`), which reads this file's last theorem
  unchanged. **The second clause of this bullet read *and over an open subset of the base it is
  `Other/Oka/Analytification/StandardEtaleFiniteness.lean`'s, at `k = 0`* until 2026-09-20**, when the
  finiteness half at every `k` was written; the absence stated by the first clause is unchanged,
  and so is the absence this bullet is about, since neither of those two files is below.
* **Nothing about the projection to `ℂ^n` at `k ≥ 1`**, which is a different statement and is
  false for a proper non-empty `X^an`;
  `Other/Oka/Analytification/StandardEtaleLocalIso.lean` records why and this file does not touch it.
* **No general étale morphism.** Every étale morphism is Zariski-locally standard étale and the
  gluing is a separate construction that nothing starts.
* **No `k ≥ 1` instance is exhibited *here*.** Nothing below produces one ; the statement is
  general in `k` and subsumes `k = 0`.
* **No implicit function theorem *relative to `X^an`*, which is the one the five sites priced.**
  One relative to `ℂ^n` is spent four links down ; step 3 is
  `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`, whose topological half is
  `Other/Oka/Analysis/Calculus/Implicit.lean`'s
  `isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter` ; and the `k = 0` line already spent
  it. **What is not here is a second one.**
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-! ### The hypersurface of `F` alone, and the `k ≥ 1` one inside it -/

/-- **The hypersurface `{F = 0} ⊆ ℂ^(n+1)`, as a presentation with one relation**:
`ComplexAnalytic.hypersurfacePresentation` over the empty base.

Spelled through `ComplexAnalytic.hypersurfacePresentation` rather than as `![F]` so that
`ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`, which is stated at that
spelling and at the empty base, applies to it with no rewriting. -/
abbrev hypersurfaceOnly : Fin 1 → MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  hypersurfacePresentation.{u} (![] : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ) F

/-- **The ideal of `{F = 0}` is contained in the ideal of the `k ≥ 1` hypersurface.**

Both are `ComplexAnalytic.presentationIdeal_hypersurfacePresentation`, a join of the base's ideal
with `(F)`; over the empty base the first summand is `⊥`. -/
theorem presentationIdeal_hypersurfaceOnly_le :
    presentationIdeal.{u} (hypersurfaceOnly.{u} (n := n) F) ≤
      presentationIdeal.{u} (hypersurfacePresentation.{u} g F) := by
  rw [presentationIdeal_hypersurfacePresentation, presentationIdeal_hypersurfacePresentation]
  refine sup_le (le_trans ?_ le_sup_right) le_sup_right
  simp [presentationIdeal]

/-- **The `k ≥ 1` hypersurface, as a subspace of `{F = 0}`.**

`ComplexAnalytic.analytificationCompare` at the containment above. It is a closed immersion, but
nothing below reads that from the construction: what is used is the cut-out datum in
`ComplexAnalytic.isCutOutBy_hypersurfaceCompare`, which carries the closed embedding as one of
its four fields. -/
abbrev hypersurfaceCompare :
    AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F) ⟶
      AnalyticSpace.analytification.{u} (hypersurfaceOnly.{u} (n := n) F) :=
  analytificationCompare.{u} (presentationIdeal_hypersurfaceOnly_le.{u} g F)

/-- **The comparison is a morphism over `ℂ^(n+1)`.**

Two morphisms into affine space agree as soon as their coordinate pullbacks do, and
`ComplexAnalytic.coordPullback_analytificationCompare_comp` is exactly that computation. -/
theorem hypersurfaceCompare_comp : hypersurfaceCompare.{u} g F ≫
      analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F) =
    analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) :=
  AnalyticSpace.hom_ext_complexAffineSpace _ _ fun i ↦
    coordPullback_analytificationCompare_comp.{u} (presentationIdeal_hypersurfaceOnly_le.{u} g F) i

/-- **The sections cutting out the `k ≥ 1` hypersurface are `F` together with the relations of the
base, read one variable up** ; as a set, which is all
`ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq` asks.

`ComplexAnalytic.hypersurfacePresentation` is a `Fin.snoc`, so this is `Fin.snoc_last` and
`Fin.snoc_castSucc` split by `Fin.lastCases`. It is stated at the *sections* and not at the
polynomials because that is where the cancellation consumes it. -/
theorem range_section_hypersurfacePresentation :
    (Set.range fun j ↦ (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (hypersurfacePresentation.{u} g F j) :
      (AnalyticSpace.complexAffineSpace.{u} (n + 1)).presheaf.obj (op ⊤))) =
      Set.range ![OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) F] ∪
        Set.range fun r : Fin k ↦ (OkaRing.ofMvPolynomial
          (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) (polyPresentation.{u} g r) :
          (AnalyticSpace.complexAffineSpace.{u} (n + 1)).presheaf.obj (op ⊤)) := by
  ext s
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · exact Or.inl ⟨0, by simp [hypersurfacePresentation]⟩
    · exact Or.inr ⟨i, by simp [hypersurfacePresentation]⟩
  · rintro (⟨j, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨Fin.last k, ?_⟩
      fin_cases j
      simp [hypersurfacePresentation]
    · exact ⟨i.castSucc, by simp [hypersurfacePresentation]⟩

/-- **The `k ≥ 1` hypersurface is cut out inside `{F = 0}` by the relations of the base, pulled
back along the inclusion of `{F = 0}` into `ℂ^(n+1)`.**

`ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq` at the two data this repository already has for
`ℂ^(n+1)`, with the set identity above. **Nothing in the tree cut a subspace out of anything but
`ℂ^n` before the cancellation landed**, and this is the first consumer of it: the two data both
point at `ℂ^(n+1)` and what is wanted is the smaller relative to the larger. -/
theorem isCutOutBy_hypersurfaceCompare : IsCutOutBy (hypersurfaceCompare.{u} g F).toLRSHom
    (fun r : Fin k ↦ (LocallyRingedSpace.Γ.map
      (analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F)).toLRSHom.op).hom
      (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (polyPresentation.{u} g r))) := by
  refine IsCutOutBy.of_comp_of_range_eq
    (isCutOutBy_analytificationInclHom_hypersurface.{u} _ F) ?_
    (range_section_hypersurfacePresentation.{u} g F)
  rw [show (hypersurfaceCompare.{u} g F).toLRSHom ≫
      (analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F)).toLRSHom =
      (analytificationInclHom.{u} (hypersurfacePresentation.{u} g F)).toLRSHom from
    congrArg AnalyticSpace.Hom.toLRSHom (hypersurfaceCompare_comp.{u} g F)]
  exact isCutOutBy_analytificationInclHom.{u} (hypersurfacePresentation.{u} g F)

/-! ### The projection, and the open it is a local isomorphism on -/

/-- **Pulling a polynomial back along the projection `ℂ^(n+1) ⟶ ℂ^n` is reading it one variable
up**, i.e. renaming along `ComplexAnalytic.localisationIncl`.

`ComplexAnalytic.Γ_map_comp_ofMvPolynomial` turns each side into an `MvPolynomial.eval₂Hom` ; the
right-hand side at the identity of `ℂ^(n+1)`, whose coordinate pullbacks are the coordinates
themselves ; and `MvPolynomial.eval₂Hom_rename` closes the gap between them.
`ComplexAnalytic.AnalyticSpace.coordPullback_proj` is where the renaming enters, and it is
`ComplexAnalytic.uliftCastSuccEmb`, which is `ComplexAnalytic.localisationIncl` on the nose. -/
theorem pullbackΓ_proj_ofMvPolynomial (q : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (AnalyticSpace.proj.{u} n).pullbackΓ
        (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) q) =
      OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (MvPolynomial.rename (localisationIncl.{u} n) q) := by
  have hl : (AnalyticSpace.proj.{u} n).pullbackΓ
      (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) q) =
      MvPolynomial.eval₂Hom (AnalyticSpace.complexAffineSpace.{u} (n + 1)).algebraMap
        (AnalyticSpace.coordPullback (AnalyticSpace.proj.{u} n)) q :=
    RingHom.congr_fun (Γ_map_comp_ofMvPolynomial.{u} (AnalyticSpace.proj.{u} n)) q
  have hr : (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1))).pullbackΓ
      (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (MvPolynomial.rename (localisationIncl.{u} n) q)) =
      MvPolynomial.eval₂Hom (AnalyticSpace.complexAffineSpace.{u} (n + 1)).algebraMap
        (AnalyticSpace.coordPullback (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1))))
        (MvPolynomial.rename (localisationIncl.{u} n) q) :=
    RingHom.congr_fun
      (Γ_map_comp_ofMvPolynomial.{u} (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1))))
      (MvPolynomial.rename (localisationIncl.{u} n) q)
  have hid : (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1))).pullbackΓ
      (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (MvPolynomial.rename (localisationIncl.{u} n) q)) =
      OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (MvPolynomial.rename (localisationIncl.{u} n) q) := by
    change (LocallyRingedSpace.Γ.map
      (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1)).toLocallyRingedSpace).op).hom _ = _
    rw [op_id, LocallyRingedSpace.Γ.map_id]
    rfl
  have hcoord : AnalyticSpace.coordPullback (AnalyticSpace.proj.{u} n) =
      AnalyticSpace.coordPullback (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1))) ∘
        localisationIncl.{u} n := by
    funext j
    rw [AnalyticSpace.coordPullback_proj]
    change _ = AnalyticSpace.coordPullback (𝟙 _) (localisationIncl.{u} n j)
    rw [show AnalyticSpace.coordPullback (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1)))
        (localisationIncl.{u} n j) = coord (localisationIncl.{u} n j) from ?_]
    · rfl
    · change (LocallyRingedSpace.Γ.map
        (𝟙 (AnalyticSpace.complexAffineSpace.{u} (n + 1)).toLocallyRingedSpace).op).hom _ = _
      rw [op_id, LocallyRingedSpace.Γ.map_id]
      rfl
  rw [hl, ← hid, hr, MvPolynomial.eval₂Hom_rename, hcoord]

/-- **`D(G · ∂F)` inside the hypersurface `{F = 0} ⊆ ℂ^(n+1)` projects to `ℂ^n` as a local
isomorphism**, for every `F` and `G` and with **no hypothesis on `g` at all**.

The derivative hypothesis of `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` is asked
at the points of the open and is true there by construction: a product does not vanish unless one
of its factors does. **This is why the open is `D(G · ∂F)` and not `D(G)`** ;
`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` supplies the derivative only at points of the `k ≥ 1`
hypersurface, and here we are on the `k = 0` one, of which that is a proper closed subset. -/
theorem isLocalIso_hypersurfaceOnly_ofRestrict_comp_proj :
    AnalyticSpace.IsLocalIso
      ((AnalyticSpace.analytification.{u} (hypersurfaceOnly.{u} (n := n) F)).ofRestrict
          (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
            (G * MvPolynomial.pderiv (localisationVar.{u} n) F)) ≫
        analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F) ≫
          AnalyticSpace.proj.{u} n) :=
  isLocalIso_hypersurface_ofRestrict_comp_proj.{u} _ F _ fun y ↦ by
    have hy := (mem_localisationOpen_iff.{u} _ _).1 y.2
    rw [map_mul] at hy
    exact (mul_ne_zero_iff.1 hy).2

/-- **On the `k ≥ 1` hypersurface, inverting the derivative as well changes nothing**:
`D(G · ∂F) = D(G)`.

`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` says the derivative is invertible at every point of
that hypersurface at which `G` is, so the second factor's open contains the first's and
`ComplexAnalytic.localisationOpen_mul` collapses the meet.

**This is what reconciles the two sides of the transport.** The source is over `D(G)` in the
`k ≥ 1` hypersurface and the target over `D(G · ∂F)` in the `k = 0` one; they are opens of
different spaces and having the same points is not an identification. What this says is that on
the `k ≥ 1` side *one formula names both opens*, so the two sides can be stated at `G · ∂F`
throughout and the source open is the comparison's preimage of the target open with no comparison
of subspaces anywhere. -/
theorem localisationOpen_mul_pderiv (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    localisationOpen.{u} (hypersurfacePresentation.{u} g F)
        (G * MvPolynomial.pderiv (localisationVar.{u} n) F) =
      localisationOpen.{u} (hypersurfacePresentation.{u} g F) G := by
  rw [localisationOpen_mul]
  refine inf_eq_left.2 fun y hy ↦ ?_
  exact (mem_localisationOpen_iff.{u} _ _).2
    (eval_pderiv_ne_zero_of_mem.{u} g F G P hF hG y ((mem_localisationOpen_iff.{u} _ _).1 hy))

/-! ### The transport -/

/-- **The family cutting out the restriction is the pullback of the relations of the base along
the projection of `D(G · ∂F)` to `ℂ^n`** ; which is what
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ` asks of its second datum.

Contravariant functoriality of the global sections twice
(`AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply`) and
`ComplexAnalytic.pullbackΓ_proj_ofMvPolynomial` once. `ComplexAnalytic.polyPresentation` is by
definition the renaming that lemma produces, so no step compares two spellings of it. -/
theorem restrictSections_hypersurfaceCompare :
    restrictSections (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
        (G * MvPolynomial.pderiv (localisationVar.{u} n) F))
      (fun r : Fin k ↦ (LocallyRingedSpace.Γ.map
        (analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F)).toLRSHom.op).hom
        (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
          (polyPresentation.{u} g r))) =
    fun r ↦ ((AnalyticSpace.analytification.{u} (hypersurfaceOnly.{u} (n := n) F)).ofRestrict
        (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
          (G * MvPolynomial.pderiv (localisationVar.{u} n) F)) ≫
      analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F) ≫
        AnalyticSpace.proj.{u} n).pullbackΓ
      (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) (g r)) := by
  funext r
  change (LocallyRingedSpace.Γ.map ((AnalyticSpace.analytification.{u}
      (hypersurfaceOnly.{u} (n := n) F)).ofRestrict _).toLRSHom.op).hom
      ((LocallyRingedSpace.Γ.map (analytificationInclHom.{u}
        (hypersurfaceOnly.{u} (n := n) F)).toLRSHom.op).hom
        (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
          (MvPolynomial.rename (localisationIncl.{u} n) (g r)))) = _
  rw [← pullbackΓ_proj_ofMvPolynomial.{u} (g r)]
  change _ = (LocallyRingedSpace.Γ.map
      (((AnalyticSpace.analytification.{u} (hypersurfaceOnly.{u} (n := n) F)).ofRestrict
            _).toLRSHom ≫
        (analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F)).toLRSHom ≫
          (AnalyticSpace.proj.{u} n).toLRSHom).op).hom _
  rw [LocallyRingedSpace.Γ_map_comp_apply, LocallyRingedSpace.Γ_map_comp_apply]

/-- **The square the transport consumes**: the map to the base followed by the base's inclusion
into `ℂ^n` is the restriction of the comparison followed by the projection of `D(G · ∂F)`.

`ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp` ; which holds for every `k` ; turns
the left-hand side into the `k ≥ 1` hypersurface's own inclusion followed by the projection, and
`ComplexAnalytic.hypersurfaceCompare_comp` factors that inclusion through `{F = 0}`. What is left
is `ComplexAnalytic.AnalyticSpace.restrictHom_fac`, read backwards. -/
theorem ofRestrict_comp_analytificationMap_comp_analytificationInclHom :
    ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
        ((Opens.map (hypersurfaceCompare.{u} g F).toLRSHom.base).obj
          (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
            (G * MvPolynomial.pderiv (localisationVar.{u} n) F))) ≫
      analytificationMap.{u} (hypersurfacePresHom.{u} g F)) ≫ analytificationInclHom.{u} g =
      AnalyticSpace.restrictHom (hypersurfaceCompare.{u} g F)
          (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
            (G * MvPolynomial.pderiv (localisationVar.{u} n) F)) ≫
        ((AnalyticSpace.analytification.{u} (hypersurfaceOnly.{u} (n := n) F)).ofRestrict
            (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
              (G * MvPolynomial.pderiv (localisationVar.{u} n) F)) ≫
          analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F) ≫
            AnalyticSpace.proj.{u} n) := by
  rw [Category.assoc, analytificationMap_hypersurfacePresHom_comp,
    ← hypersurfaceCompare_comp.{u} g F, ← Category.assoc, ← Category.assoc,
    ← AnalyticSpace.restrictHom_fac]
  simp only [Category.assoc]

/-- **`D(G · ∂F)` inside the `k ≥ 1` hypersurface maps to the base's analytification as a local
isomorphism**, for every `F` and `G` and with no étale hypothesis.

`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ` at the square above, the
base's own cut-out datum in `ℂ^n` and the restriction of
`ComplexAnalytic.isCutOutBy_hypersurfaceCompare`. **The étale hypotheses enter nowhere in this
statement**: they are needed only to know that the open here is the `D(G)` the comparison with
`ComplexAnalytic.etalePresHom` is stated at, which is
`ComplexAnalytic.localisationOpen_mul_pderiv` and happens one theorem below. -/
theorem isLocalIso_ofRestrict_comp_analytificationMap : AnalyticSpace.IsLocalIso
    ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
        ((Opens.map (hypersurfaceCompare.{u} g F).toLRSHom.base).obj
          (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
            (G * MvPolynomial.pderiv (localisationVar.{u} n) F))) ≫
      analytificationMap.{u} (hypersurfacePresHom.{u} g F)) := by
  haveI := isLocalIso_hypersurfaceOnly_ofRestrict_comp_proj.{u} F G
  refine AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ
    (ofRestrict_comp_analytificationMap_comp_analytificationInclHom.{u} g F G)
    (isCutOutBy_analytificationInclHom.{u} g) ?_
  rw [← restrictSections_hypersurfaceCompare.{u} g F G]
  exact (isCutOutBy_hypersurfaceCompare.{u} g F).restrictOpen _

/-- **The pullback of `D(G · ∂F)` is `D(G)`.**

The comparison carries a polynomial section of `{F = 0}` to the same polynomial's section of the
`k ≥ 1` hypersurface ; `ComplexAnalytic.polyToGlobal_eq_eval₂Hom` and
`ComplexAnalytic.AnalyticSpace.pullbackΓ_eval₂` reduce that to the coordinates, where it is
`ComplexAnalytic.coordPullback_analytificationCompare_comp` ; and
`ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ` turns a section identity into one of
non-vanishing loci. Then `ComplexAnalytic.localisationOpen_mul_pderiv` deletes the derivative. -/
theorem comap_localisationOpen_hypersurfaceCompare
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    (Opens.map (hypersurfaceCompare.{u} g F).toLRSHom.base).obj
        (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
          (G * MvPolynomial.pderiv (localisationVar.{u} n) F)) =
      localisationOpen.{u} (hypersurfacePresentation.{u} g F) G := by
  have hcoord (i : ULift.{u} (Fin (n + 1))) :
      (hypersurfaceCompare.{u} g F).pullbackΓ
        (analytificationCoord.{u} (hypersurfaceOnly.{u} (n := n) F) i) =
        analytificationCoord.{u} (hypersurfacePresentation.{u} g F) i :=
    (AnalyticSpace.coordPullback_comp (hypersurfaceCompare.{u} g F)
        (analytificationInclHom.{u} (hypersurfaceOnly.{u} (n := n) F)) i).symm.trans
      (coordPullback_analytificationCompare_comp.{u}
        (presentationIdeal_hypersurfaceOnly_le.{u} g F) i)
  have hpoly (q : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
      (hypersurfaceCompare.{u} g F).pullbackΓ
          (polyToGlobal.{u} (hypersurfaceOnly.{u} (n := n) F) q) =
        polyToGlobal.{u} (hypersurfacePresentation.{u} g F) q := by
    rw [polyToGlobal_eq_eval₂Hom, polyToGlobal_eq_eval₂Hom]
    simpa using
      (AnalyticSpace.pullbackΓ_eval₂ (hypersurfaceCompare.{u} g F)
        (analytificationCoord.{u} (hypersurfaceOnly.{u} (n := n) F)) q).trans
        (congrArg (fun a ↦ MvPolynomial.eval₂ _ a q) (funext hcoord))
  have hcomap : (Opens.map (hypersurfaceCompare.{u} g F).toLRSHom.base).obj
      (localisationOpen.{u} (hypersurfaceOnly.{u} (n := n) F)
        (G * MvPolynomial.pderiv (localisationVar.{u} n) F)) =
      localisationOpen.{u} (hypersurfacePresentation.{u} g F)
        (G * MvPolynomial.pderiv (localisationVar.{u} n) F) := by
    rw [localisationOpen, localisationOpen, ← hpoly, AnalyticSpace.nonvanishing_pullbackΓ]
  rw [hcomap]
  exact localisationOpen_mul_pderiv.{u} g F G P hF hG

/-- **The analytification of a standard étale morphism over a presented base is a local
isomorphism onto that base**, at every `k`.

The statement taxis #1113's comparison functor consumes and the one the five sites priced as
needing an implicit function theorem relative to `X^an`; it needs none, and spends only the one
relative to `ℂ^n` that the `k = 0` line already spends. Those five sites are listed in this file's
module docstring, and they sit in **four** files ; this sentence said *five files* until the
count was replaced by the list.
`ComplexAnalytic.etaleAnalytificationIso_hom_comp` ; an equation already in the tree and general
in `k` ; replaces the étale analytification by `D(G)` in the
hypersurface over the base, `ComplexAnalytic.comap_localisationOpen_hypersurfaceCompare` says
that `D(G)` is the open the transport landed on, and
`ComplexAnalytic.AnalyticSpace.isLocalIso_comp` composes the result with an isomorphism.

**The target is `X^an` and not `ℂ^n`.** Composed with `ComplexAnalytic.analytificationInclHom g`
this statement is false at `k ≥ 1` for every `g` with a proper non-empty zero locus, which
`Other/Oka/Analytification/StandardEtaleLocalIso.lean` proves; the two are different theorems and only
this one is about the morphism a cover is. -/
theorem isLocalIso_analytificationMap_etalePresHom
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    AnalyticSpace.IsLocalIso (analytificationMap.{u} (etalePresHom.{u} g F G)) := by
  haveI : AnalyticSpace.IsLocalIso
      ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
        (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
          analytificationMap.{u} (hypersurfacePresHom.{u} g F)) :=
    comap_localisationOpen_hypersurfaceCompare.{u} g F G P hF hG ▸
      isLocalIso_ofRestrict_comp_analytificationMap.{u} g F G
  haveI : AnalyticSpace.IsLocalIso (etaleAnalytificationIso.{u} g F G).hom :=
    AnalyticSpace.isLocalIso_of_isIso _
  rw [← etaleAnalytificationIso_hom_comp.{u} g F G]
  infer_instance

end

end ComplexAnalytic

end
