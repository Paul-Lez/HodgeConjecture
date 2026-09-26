/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.SimpleZeroPolynomial
public import Other.Oka.GermDerivative
public import Other.Oka.Analysis.Calculus.Implicit

/-!
# A hypersurface with a simple zero everywhere projects by a local isomorphism

`Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` proves that a hypersurface `i : X ⟶ ℂ^(n+1)` with a
simple zero along the last axis at a point projects **isomorphically on the stalk** there, and
says in its own `## What is not here` that *"nothing below says anything about the underlying map
of `i ≫ p`, not even that it is open"*. This file supplies that missing half and assembles the
two: with the simple-zero condition at **every** point of `X`, the composite `i ≫ p` is a
`ComplexAnalytic.AnalyticSpace.IsLocalIso`.

The topological half is the implicit function theorem, and it is not proved here either: it is
`isLocalHomeomorph_coordProj_comp_of_isEmbedding` in `Other/Oka/Analysis/Calculus/Implicit.lean`, a
statement about level sets of a strictly differentiable function on `ι → 𝕜` with no complex
analysis in it. What this file does is discharge that theorem's four hypotheses from
`ComplexAnalytic.IsCutOutBy`, which is one paragraph each:

* **the embedding.** `IsCutOutBy.isClosedEmbedding` is one of the four fields.
* **the level set.** `IsCutOutBy.range_base` says the image is where every germ is a non-unit,
  and `germ_mem_maximalIdeal_iff` turns that into the vanishing of the function
  (`ComplexAnalytic.range_base_eq_zeroSet`).
* **strict differentiability.** `OkaRing.analyticAt_toGlobalFun` and
  `AnalyticAt.hasStrictFDerivAt`; the cutting section is holomorphic on all of `ℂ^(n+1)`, so this
  holds at every point and not only on the hypersurface.
* **the nonvanishing derivative**, and this is the step that had nothing to stand on:
  `OkaRing.coeff_single_one_germ` (`Other/Oka/GermDerivative.lean`) says that the coefficient of the
  last variable in the germ **is** the derivative in that direction, for an arbitrary holomorphic
  cutting section. So the hypothesis below is the same one the stalk half already takes, with no
  polynomial and no extra data.

## Why the hypothesis is at every point, and the stalk half's is not

`ComplexAnalytic.AnalyticSpace.IsLocalIso` asks for a local homeomorphism, which is a condition on
the *whole* space, so a pointwise hypothesis cannot suffice for it. The stalk field is pointwise
and this file quantifies its input; the topological field is not, and the implicit function
theorem is applied at each point separately with the hypothesis at that point. Nothing here is
uniform in the point, and nothing needs to be.

## Main results

- `ComplexAnalytic.range_base_eq_zeroSet`: **the image of a cut-out by one section is the zero
  set of that section**, as a set of functions rather than as a set of germs.
- `ComplexAnalytic.base_comp_uliftProj`: the underlying map of `i ≫ p` is `i.base` followed by
  restriction of coordinates.
- `ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff`: **the underlying map of
  `i ≫ p` is a local homeomorphism** when the linear coefficient of the germ is nonzero at every
  point, and `ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv`, the same for a
  polynomial cutting section, with the hypothesis read as `MvPolynomial.pderiv`.
- `ComplexAnalytic.isLocalIso_comp_proj_of_coeff` and
  `ComplexAnalytic.isLocalIso_comp_proj_of_pderiv`: **`i ≫ p` is a local isomorphism of complex
  analytic spaces**, the two halves together.
- `ComplexAnalytic.range_base_ofRestrict_eq_zeroSet_inter`: **the image of an open subspace of the
  hypersurface is the zero set met with an open subset of `ℂ^(n+1)`.**
- `ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff` and
  `ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_pderiv`: **the same
  topological half after restricting the source to an open subspace**, with the hypothesis asked
  only at the points of that subspace.
- `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_coeff` and
  `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`: **an open subspace of the
  hypersurface projects as a local isomorphism**, which is what a standard étale presentation
  needs, since it inverts a polynomial and so supplies the simple-zero hypothesis on an open
  subset of the hypersurface and nowhere else.
- `ComplexAnalytic.not_mem_range_uliftCastSuccEmb` and
  `ComplexAnalytic.mem_range_uliftCastSuccEmb`: the last coordinate is the only one the
  projection forgets.

## What is not here

* **No finiteness, and so no `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`.** A local isomorphism
  is one of that class's two fields; the other is `ComplexAnalytic.AnalyticSpace.IsFinite`, and
  for the projection of a hypersurface it is the monic case of
  `Other/Oka/Analytification/MonicHypersurface.lean`, which asks for a hypothesis nothing below takes.
  **The gap is real and not an artefact of the proof**, and the reason is a hypersurface this
  file's hypothesis admits: `z₀z₁ = 1` has `∂/∂z₁ = z₀`, which is nonzero at every point of it,
  so the results below apply; and its projection to the `z₀`-line misses the origin, so the image
  is not closed and the map is not `IsFinite`. **That last sentence is reasoning about a set and
  is compiled nowhere** ; no declaration in this repository states it.
* **Nothing about a hypersurface inside an open subset of the *ambient* space.** `i` maps into the
  whole of `ℂ^(n+1)`, so the cutting section is entire, and that is unchanged by the restricted
  statements above: those restrict the **source**, and the section they cut it out by is still an
  entire one. The stalk half has an open-*base* version in
  `Other/Oka/AnalyticSpace/OpenBaseProjection.lean` ; a cylinder over an open `V ⊆ ℂ^n`, pulled back ;
  and the topological half still has none. **The two restrictions are different and neither
  subsumes the other**, which the earlier form of this bullet did not distinguish: `D(G)` for a
  `G` involving the fibre variable is not a cylinder over anything, and an open subspace of the
  source is not a preimage from the base.
* **No converse.** Nothing says that a hypersurface whose projection is a local isomorphism has a
  simple zero. The hypothesis is sufficient and is not claimed to be necessary.
* **No statement about the image.** A local homeomorphism need not be surjective and need not be
  injective, and nothing below says which points of `ℂ^n` are hit or how often.
* **Nothing here is a statement about the projection alone, and the hypersurface is what makes
  the difference.** `ComplexAnalytic.proj` itself is **not** a local isomorphism, so no result
  below is an instance of one about `p`, and the simple-zero hypothesis is what rules out the
  collapsing the projection exhibits.
* **Nothing is moved.** `ComplexAnalytic.not_mem_range_uliftCastSuccEmb` and
  `ComplexAnalytic.mem_range_uliftCastSuccEmb` are facts about `ComplexAnalytic.uliftCastSuccEmb`
  alone and their home is `Other/Oka/AnalyticSpace/ProjectionStalk.lean`, where that embedding is
  defined; they are here because this is their only consumer, and a second consumer is what
  should move them.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MvPowerSeries

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### The last coordinate is the one the projection forgets -/

/-- **The projection does not remember the last coordinate**: `ULift.up (Fin.last n)` is outside
the range of `ComplexAnalytic.uliftCastSuccEmb`, because `Fin.castSucc` lands strictly below
`Fin.last`. -/
theorem not_mem_range_uliftCastSuccEmb :
    ULift.up.{u} (Fin.last n) ∉ Set.range (uliftCastSuccEmb.{u} n) := by
  rintro ⟨k, hk⟩
  exact absurd (ULift.up.inj hk) (Fin.castSucc_lt_last k.down).ne

/-- **The projection remembers every other coordinate**: an index other than
`ULift.up (Fin.last n)` is in the range of `ComplexAnalytic.uliftCastSuccEmb`. -/
theorem mem_range_uliftCastSuccEmb {m : ULift.{u} (Fin (n + 1))}
    (hm : m ≠ ULift.up.{u} (Fin.last n)) : m ∈ Set.range (uliftCastSuccEmb.{u} n) := by
  obtain ⟨m₀⟩ := m
  have h : m₀ ≠ Fin.last n := fun h ↦ hm (by rw [h])
  obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.2 h
  exact ⟨ULift.up k, ULift.ext _ _ hk⟩

/-! ### The hypersurface, as a level set -/

variable {X : LocallyRingedSpace.{u}} {i : X ⟶ complexAffineSpace.{u} (n + 1)}
  {F : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))}

/-- **A cut-out by one section has the zero set of that section for its image**, stated with the
section read as a function on `ℂ^(n+1)` rather than as a germ.

`ComplexAnalytic.range_base_eq_of_isCutOutBy` is the same fact with the right-hand side written
through `OkaRing.evalHom`; that spelling is what a stalk argument wants and this one is what the
implicit function theorem wants, since its level set is a set of points at which a *function*
takes a value. -/
theorem range_base_eq_zeroSet (hcut : IsCutOutBy i ![F]) :
    Set.range (i.base : X → (ULift.{u} (Fin (n + 1)) → ℂ)) =
      {z : ULift.{u} (Fin (n + 1)) → ℂ | F.toGlobalFun ⊤ z = 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change F.toGlobalFun ⊤ _ = 0
    rw [OkaRing.toGlobalFun_eq_evalHom F (show (i.base x : ULift.{u} (Fin (n + 1)) → ℂ) ∈
      (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial)]
    simpa using hcut.evalHom_eq_zero x 0
  · intro h
    have h' : OkaRing.evalHom (U := ⊤) (x := (z : ULift.{u} (Fin (n + 1)) → ℂ)) trivial F = 0 := by
      rw [← OkaRing.toGlobalFun_eq_evalHom]
      exact h
    change z ∈ Set.range (i.base : X → (ULift.{u} (Fin (n + 1)) → ℂ))
    rw [hcut.range_base]
    intro j
    fin_cases j
    exact (germ_mem_maximalIdeal_iff (U := ⊤) trivial F).2 h'

/-- **The underlying map of `i ≫ p` is `i.base` followed by restriction of coordinates**, which
is `ComplexAnalytic.okaMapFun_coordEmb` at each point. -/
theorem base_comp_uliftProj :
    ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base : X → _) =
      fun x ↦ (i.base x : ULift.{u} (Fin (n + 1)) → ℂ) ∘ (uliftCastSuccEmb.{u} n) :=
  funext fun _ ↦ okaMapFun_coordEmb _ _

/-! ### The topological half -/

/-- **The projection of a hypersurface with a simple zero at every point is a local
homeomorphism.**

This is the half `Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` records as absent. It is the implicit
function theorem, in the form `isLocalHomeomorph_coordProj_comp_of_isEmbedding`: the hypersurface
is the level set `{F = 0}` by `ComplexAnalytic.range_base_eq_zeroSet`, `i.base` embeds `X` onto
it, `F` is strictly differentiable everywhere because it is holomorphic, and the derivative in the
last direction is the coefficient in the hypothesis by
`OkaRing.coeff_single_one_germ`. -/
theorem isLocalHomeomorph_base_comp_uliftProj_of_coeff (hcut : IsCutOutBy i ![F])
    (hlin : ∀ x : X, MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    IsLocalHomeomorph ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base : X → _) := by
  rw [base_comp_uliftProj]
  refine isLocalHomeomorph_coordProj_comp_of_isEmbedding (f := F.toGlobalFun ⊤)
    (f' := fun z ↦ fderiv ℂ (F.toGlobalFun ⊤) z) hcut.isClosedEmbedding.isEmbedding
    (fun m hm ↦ mem_range_uliftCastSuccEmb hm) not_mem_range_uliftCastSuccEmb
    (range_base_eq_zeroSet hcut) (fun z _ ↦ (F.analyticAt_toGlobalFun trivial).hasStrictFDerivAt)
    fun z hz ↦ ?_
  have hmem : z ∈ Set.range (i.base : X → (ULift.{u} (Fin (n + 1)) → ℂ)) := by
    rw [range_base_eq_zeroSet hcut]; exact hz
  obtain ⟨x, rfl⟩ := hmem
  rw [← OkaRing.coeff_single_one_germ]
  exact hlin x

/-- **The same for a polynomial cutting section**, with the hypothesis read as a partial
derivative rather than as a Taylor coefficient.

`LocalOkaRing.coeff_single_one_ofMvPolynomial`, exactly as in
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_pderiv`. -/
theorem isLocalHomeomorph_base_comp_uliftProj_of_pderiv
    {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P])
    (hlin : ∀ x : X, MvPolynomial.eval (i.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    IsLocalHomeomorph ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base : X → _) := by
  refine isLocalHomeomorph_base_comp_uliftProj_of_coeff hcut fun x ↦ ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin x

/-! ### Restricting the source -/

/-- **The image of an open subspace of the hypersurface is the zero set met with an open subset of
the ambient space.**

This is the whole of what a *restriction of the source* costs, and it is what
`Other/Oka/AnalyticSpace/OpenBaseProjection.lean` is not: that file restricts the **base** and pulls
back, so its open is a cylinder, while `U` here is any open of `X` whatever and the `Ω` it
produces is an open of `ℂ^(n+1)` with no product structure asked of it. The `Ω` exists because
`i.base` is an embedding, so every open of `X` is the preimage of one; it is not unique and
nothing below needs it to be. -/
theorem range_base_ofRestrict_eq_zeroSet_inter (hcut : IsCutOutBy i ![F]) (U : Opens X) :
    ∃ Ω : Set (ULift.{u} (Fin (n + 1)) → ℂ), IsOpen Ω ∧
      Set.range ((X.ofRestrict U.isOpenEmbedding ≫ i).base :
        X.restrict U.isOpenEmbedding → (ULift.{u} (Fin (n + 1)) → ℂ)) =
        {z : ULift.{u} (Fin (n + 1)) → ℂ | F.toGlobalFun ⊤ z = 0} ∩ Ω := by
  obtain ⟨Ω, hΩ, hUΩ⟩ := hcut.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.1 U.isOpen
  refine ⟨Ω, hΩ, ?_⟩
  have hr : Set.range ((X.ofRestrict U.isOpenEmbedding ≫ i).base :
      X.restrict U.isOpenEmbedding → (ULift.{u} (Fin (n + 1)) → ℂ)) =
      (i.base : X → (ULift.{u} (Fin (n + 1)) → ℂ)) '' (U : Set X) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  rw [hr, ← hUΩ, Set.image_preimage_eq_inter_range, range_base_eq_zeroSet hcut]
  exact Set.inter_comm _ _

/-- **The projection of an open subspace of a hypersurface is a local homeomorphism**, at the
simple-zero hypothesis asked only at the points of that open subspace.

This is the statement three module docstrings recorded as absent ; the hypersurface met with
`D(G)` of a standard étale presentation is a restriction of the *source*, and
`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` supplies the derivative only there, so
`ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff`, whose hypothesis is at every
point of `X`, cannot be applied.

**It is not a corollary of that theorem and it is not a composition.** A local homeomorphism
precomposed with an open immersion is a local homeomorphism, but the hypothesis of the
unrestricted statement is exactly what a restricted source does not supply, so nothing is
available to precompose with. What the proof needs instead is the implicit function theorem on a
*relatively open piece* of the level set, which is
`isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter`, and `Ω` comes from
`ComplexAnalytic.range_base_ofRestrict_eq_zeroSet_inter` above.

**One level down that restriction is free, and this is the level at which it stops being free.**
`isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter` is a twenty-line corollary of its own
unrestricted form, because the `f` there is a bare function and can be replaced by one whose
level set is already `{f = c} ∩ Ω`; its docstring gives the replacement. Here `F` is an
`OkaRing` section, so it is holomorphic, and there is in general no holomorphic `F'` on `ℂ^(n+1)`
with `{F' = 0} = {F = 0} ∩ Ω` for an arbitrary open `Ω` ; the zero set of a holomorphic function
is closed and `{F = 0} ∩ Ω` need not be. **That is an argument and no counterexample is compiled
for it**; what is compiled is that this statement is proved from the mirror-tree one and not from
`ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff`. -/
theorem isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff (hcut : IsCutOutBy i ![F])
    (U : Opens X)
    (hlin : ∀ x : X.restrict U.isOpenEmbedding,
      MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show (X.ofRestrict U.isOpenEmbedding ≫ i).base x ∈
          (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    IsLocalHomeomorph ((X.ofRestrict U.isOpenEmbedding ≫ i ≫
      okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base :
        X.restrict U.isOpenEmbedding → _) := by
  obtain ⟨Ω, hΩ, hrange⟩ := range_base_ofRestrict_eq_zeroSet_inter hcut U
  rw [← Category.assoc, base_comp_uliftProj]
  refine isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter
    (hcut.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal) hΩ
    (f := F.toGlobalFun ⊤) (f' := fun z ↦ fderiv ℂ (F.toGlobalFun ⊤) z)
    (fun m hm ↦ mem_range_uliftCastSuccEmb hm) not_mem_range_uliftCastSuccEmb hrange
    (fun z _ _ ↦ (F.analyticAt_toGlobalFun trivial).hasStrictFDerivAt) fun z hzΩ hz ↦ ?_
  have hmem : z ∈ Set.range ((X.ofRestrict U.isOpenEmbedding ≫ i).base :
      X.restrict U.isOpenEmbedding → (ULift.{u} (Fin (n + 1)) → ℂ)) := by
    rw [hrange]; exact ⟨hz, hzΩ⟩
  obtain ⟨x, rfl⟩ := hmem
  rw [← OkaRing.coeff_single_one_germ]
  exact hlin x

/-- **The same for a polynomial cutting section**, by the rewrite
`LocalOkaRing.coeff_single_one_ofMvPolynomial` that
`ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv` makes at the unrestricted
hypothesis. -/
theorem isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_pderiv
    {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (U : Opens X)
    (hlin : ∀ x : X.restrict U.isOpenEmbedding,
      MvPolynomial.eval ((X.ofRestrict U.isOpenEmbedding ≫ i).base x)
        (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    IsLocalHomeomorph ((X.ofRestrict U.isOpenEmbedding ≫ i ≫
      okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base :
        X.restrict U.isOpenEmbedding → _) := by
  refine isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff hcut U fun x ↦ ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin x

/-! ### The two halves together -/

section AnalyticSpaceLevel

variable {W : AnalyticSpace.{u}} {i' : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1)}

/-- **The projection of a hypersurface with a simple zero at every point is a local isomorphism
of complex analytic spaces.**

The two fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso` are
`ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff` and
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff`, and they take the same hypothesis ; the
first at every point at once, the second at one point at a time.
`ComplexAnalytic.AnalyticSpace.proj` is the projection as a morphism of complex analytic spaces,
whose underlying morphism of locally ringed spaces is the `ComplexAnalytic.okaMapHom` the two
halves are stated for.

**The name has no `AnalyticSpace.` prefix and that is not an oversight**; the reason is a
shadowed identifier and it is worth knowing for this file's neighbours. Inside the
`ComplexAnalytic.AnalyticSpace` namespace ; entered by a dotted declaration name or by
`namespace AnalyticSpace`, it makes no difference ; `Opens` does not resolve to
`TopologicalSpace.Opens`. It resolves to `ComplexAnalytic.AnalyticSpace.Opens`
(`Other/Oka/AnalyticSpace/Basic.lean`), the open sets *of a complex analytic space*, whose argument is
an `AnalyticSpace` and not a type. The section variable `F` above is declared with the plain
spelling, `OkaRing (⊤ : Opens (ULift (Fin (n + 1)) → ℂ))`, so **every declaration in that
namespace that mentions `F` re-elaborates that binder against the wrong `Opens`.** Declarations
there that do not mention it are unaffected.

**How loudly that fails depends on where the spelling sits.** Written out in the statement itself
it is a hard `Application type mismatch … in the application Opens (ULift (Fin (n + 1)) → ℂ)`.
In the `variable` binder it is recovered as `sorryAx` with no error reported at all, and the
declaration is then either added with `sorryAx` in its *statement* ; that is what happens when
`F` appears only under `ComplexAnalytic.IsCutOutBy` ; or dropped from the environment outright,
which is what happens here, `#check` on the name failing afterwards.
`theorem AnalyticSpace.foo (h : F = F) : True := trivial` is the whole reproduction, and writing
`TopologicalSpace.Opens` in that binder removes it.

**The recovered form is caught by CI every time; the dropped form is caught only by accident.**
`.orchestra/validation.sh` runs `lake build --wfail || exit 1`, and the recovered form leaves
`sorryAx` in its own statement and warns about it, so that one is always `error: build failed`.
**The drop reports nothing of its own.** What `--wfail` escalates there is a side effect ; the
unused-variable linter firing on a binder of the theorem that has just vanished ; so a
declaration with no binder to flag goes silently. Appended to this section,

```lean
theorem AnalyticSpace.zzz_nohyp : F = F := rfl
```

elaborates with no output and exit 0, `lake build --wfail` on this module is green, and a
`#check` on the name afterwards fails: it was never added. Where the drop *is* caught, what
misleads is the *message*, which names an unused variable rather than a missing theorem, so a
reader who takes `--wfail` output for noise loses it. **What catches every form is a count of
the declarations**: `scripts/DumpOkaDecls.lean` for an unguarded name, and for a guarded one
the guard itself, since `#print axioms` on a name the environment does not have is an error. -/
theorem isLocalIso_comp_proj_of_coeff (hcut : IsCutOutBy i'.toLRSHom ![F])
    (hlin : ∀ x : W, MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show i'.toLRSHom.base x ∈
          (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    AnalyticSpace.IsLocalIso (i' ≫ AnalyticSpace.proj.{u} n) :=
  ⟨isLocalHomeomorph_base_comp_uliftProj_of_coeff hcut hlin,
    fun x ↦ isIso_stalkMap_comp_uliftProj_of_coeff hcut x (hlin x)⟩

/-- **The same for a polynomial cutting section.** This is the form the standard étale line
consumes: `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces exactly this hypothesis at a point
of the hypersurface, from `StandardEtalePair`'s `cond` field. -/
theorem isLocalIso_comp_proj_of_pderiv {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}
    (hcut : IsCutOutBy i'.toLRSHom ![OkaRing.ofMvPolynomial ⊤ P])
    (hlin : ∀ x : W, MvPolynomial.eval (i'.toLRSHom.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    AnalyticSpace.IsLocalIso (i' ≫ AnalyticSpace.proj.{u} n) :=
  ⟨isLocalHomeomorph_base_comp_uliftProj_of_pderiv hcut hlin,
    fun x ↦ isIso_stalkMap_comp_uliftProj_of_pderiv hcut x (hlin x)⟩

/-- **An open subspace of a hypersurface with a simple zero at each of its own points projects
as a local isomorphism of complex analytic spaces.**

The two fields come from opposite places and it is worth saying which, because the asymmetry is
the content of this section. The topological one is
`ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff`, which is the
implicit function theorem on a relatively open piece of the level set and is not reached from the
unrestricted statement ; **though that is a fact about *this* level and not about the mirror-tree
theorem it rests on**, which is a twenty-line corollary of its own unrestricted form; the
docstring of that theorem above says why the two levels differ. **The stalk one needed nothing new
and never did.** `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff` is
already quantified one point at a time, so it applies at `x.1` with the hypothesis asked only
there, and the open immersion contributes an isomorphism by
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`. Three module docstrings recorded the
two halves as equally absent across a restriction of the source; only one of them was.

**This is not `ComplexAnalytic.isLocalIso_comp_proj_of_coeff` composed with the open immersion.**
That composition is available ; `isLocalIso_ofRestrict` and
`ComplexAnalytic.AnalyticSpace.isLocalIso_comp` give it in one `infer_instance` ; and it is not
this, because it needs the simple-zero hypothesis at **every** point of `W`. What a standard
étale presentation supplies is the hypothesis on `D(G)` only, which is exactly a `U`. -/
theorem isLocalIso_ofRestrict_comp_proj_of_coeff (hcut : IsCutOutBy i'.toLRSHom ![F])
    (U : W.Opens)
    (hlin : ∀ x : W.restrict U, MvPowerSeries.coeff
      (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show i'.toLRSHom.base x.1 ∈
          (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    AnalyticSpace.IsLocalIso (W.ofRestrict U ≫ i' ≫ AnalyticSpace.proj.{u} n) where
  isLocalHomeomorph := isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff hcut _ hlin
  isIso_stalkMap x := by
    have h : (W.ofRestrict U ≫ i' ≫ AnalyticSpace.proj.{u} n).toLRSHom =
        (W.ofRestrict U).toLRSHom ≫ (i' ≫ AnalyticSpace.proj.{u} n).toLRSHom := rfl
    rw [h, LocallyRingedSpace.stalkMap_comp]
    exact IsIso.comp_isIso' (isIso_stalkMap_comp_uliftProj_of_coeff hcut x.1 (hlin x))
      (AnalyticSpace.isIso_stalkMap_ofRestrict W U x)

/-- **The same for a polynomial cutting section.** This is the form the standard étale line
consumes: the hypersurface is `ComplexAnalytic.hypersurfacePresentation`'s and the `U` is the
`D(G)` that presentation is localised at, on which ; and only on which ;
`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces the derivative. -/
theorem isLocalIso_ofRestrict_comp_proj_of_pderiv
    {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}
    (hcut : IsCutOutBy i'.toLRSHom ![OkaRing.ofMvPolynomial ⊤ P]) (U : W.Opens)
    (hlin : ∀ x : W.restrict U, MvPolynomial.eval (i'.toLRSHom.base x.1)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    AnalyticSpace.IsLocalIso (W.ofRestrict U ≫ i' ≫ AnalyticSpace.proj.{u} n) where
  isLocalHomeomorph :=
    isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_pderiv hcut _ hlin
  isIso_stalkMap x := by
    have h : (W.ofRestrict U ≫ i' ≫ AnalyticSpace.proj.{u} n).toLRSHom =
        (W.ofRestrict U).toLRSHom ≫ (i' ≫ AnalyticSpace.proj.{u} n).toLRSHom := rfl
    rw [h, LocallyRingedSpace.stalkMap_comp]
    exact IsIso.comp_isIso' (isIso_stalkMap_comp_uliftProj_of_pderiv hcut x.1 (hlin x))
      (AnalyticSpace.isIso_stalkMap_ofRestrict W U x)

end AnalyticSpaceLevel

end ComplexAnalytic

end
