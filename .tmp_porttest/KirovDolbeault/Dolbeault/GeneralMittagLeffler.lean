/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.GlobalResidueConstruct
import KirovDolbeault.Dolbeault.FormResidueTheorem

/-!
# Forster §17.2 — the general Mittag–Leffler distribution of 1-forms and its residue

This file builds the **general** Mittag–Leffler distribution of 1-forms (Forster §17.2), the
foundation the Cousin/∂̄ residue functional `CousinResidueData.resCocycle` needs.  The existing
`MittagLefflerForm` (`Jacobians.Dolbeault.MittagLeffler`) carries a **single global** principal-part
function `g : X → ℂ` (the `α·g` shape).  As two prior agents confirmed, that shape **cannot** represent
the lift of a *general* Čech 1-cocycle, whose connecting-map distribution is a *family* of **local**
meromorphic forms `ωᵢ = gᵢ·ω₀` (one per cover patch `Uᵢ`) with **holomorphic differences**
`ωᵢ − ωⱼ` on the overlaps — exactly Forster's `μ = (ωᵢ) ∈ C⁰(𝔘, ℳ⁽¹⁾)` with `δμ ∈ Z¹(𝔘, Ω)`.

## The mathematics (Forster 17.2, verbatim)

> Let `μ = (ωᵢ)` be a cochain of meromorphic 1-forms whose differences `ωᵢ − ωⱼ` are *holomorphic*
> on `Uᵢ ∩ Uⱼ` (`δμ ∈ Z¹(𝔘, Ω)`).  For a point `a`, choose `i` with `a ∈ Uᵢ` and set
> `Resₐ(μ) := Resₐ(ωᵢ)`.  This is independent of `i` (two local forms differ by a holomorphic form,
> which has residue `0`).  On a compact `X` only finitely many `a` have `Resₐ(μ) ≠ 0`, so
> `Res(μ) := ∑ₐ Resₐ(μ)`.

We realise `ωᵢ = gᵢ·ω₀` for a fixed global holomorphic `ω₀ : HolomorphicOneForms X` and local
principal-part functions `gᵢ : X → ℂ` (this is the Forster §17.4 shape — every meromorphic 1-form is
`f·ω₀`; the residue calculus is the proven `formFnResidue ω₀ gᵢ a`).  A `GeneralMLDistribution` then
bundles: the cover `(Uᵢ)`, the local principal parts `(gᵢ)`, the finite pole set, a designated patch
`patch a ∋ a` for each pole, the holomorphic-difference condition, and the isolated-singularity /
off-poles holomorphy conditions.  Its residue `res := ∑ₐ Resₐ(ωᵢ)` reads the genuine **meromorphic**
local residue `formFnResidue ω₀ g_{patch a} a` (NOT a smooth-junk value — `formFnResidue` is the
Laurent `c₋₁` contour residue, well-defined because `g_{patch a}`'s chart-pullback is meromorphic at
`a`), and is **patch-independent** by `formFnResidue_eq_of_analyticAt_sub` (the holomorphic-difference
property).

## What this file delivers (all complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `GeneralMLDistribution ω₀` — the general distribution structure (a TRUE, non-vacuous bundle; the
  holomorphic single-`α·g` `MittagLefflerForm` embeds, `ofMittagLefflerForm`).
* `GeneralMLDistribution.resAtPole` / `res` — the per-pole and total residue, with **patch
  independence** (`resAtPole_eq_of_mem`) — Forster's well-definedness of `Resₐ(μ)`.
* `res_eq_zero_of_globalMeromorphic` — **the coboundary vanishing**: a distribution all of whose local
  parts come from a *single global* meromorphic function `f` (`gᵢ =ᶠ f` near each pole) has
  `res = 0` — this is the `∑Res = 0` content (Gate A) that makes the residue descend to cohomology
  classes.  It is *derived* from `FormResidueTheorem` (the manifold trace residue theorem) and the
  per-pole holomorphic-difference reduction.
* non-vacuity (`ofMittagLefflerForm`, `res_ofMittagLefflerForm`): the `α·g` `MittagLefflerForm`
  (in particular the holomorphic/empty one) is a `GeneralMLDistribution`, confirming the structure is
  inhabited at genuine (non-trivial pole-count) data.

This is the **foundation** the Cousin/∂̄ connecting map produces (a cocycle ↦ a `GeneralMLDistribution`,
the genuinely-greenfield ∂̄ atom isolated separately).

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.2–17.3.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The general Mittag–Leffler distribution of 1-forms `ω₀·gᵢ` -/

/-- **A general Mittag–Leffler distribution of 1-forms** (Forster §17.2), in the `ωᵢ = gᵢ·ω₀` shape of
Forster §17.4: a finite cover `(Uᵢ)` carrying a *local* principal-part function `gᵢ : X → ℂ` on each
patch, with holomorphic differences `gᵢ − gⱼ` on overlaps and finitely many poles.

* `ι`, `U` — the (finite) index and the cover opens.
* `g i` — the local principal-part function on `Uᵢ` (so `ωᵢ = gᵢ·ω₀`).
* `poles` — the finite pole set.
* `patch a` — for each pole `a`, a designated index with `a ∈ U (patch a)` (`patch_mem`); the residue
  reads `ωᵢ = g_{patch a}·ω₀` there.  Patch-independence is *proved* (`resAtPole_eq_of_mem`).
* `holoDiff` — **the Mittag–Leffler holomorphic-difference condition**: on every overlap, `gᵢ − gⱼ`'s
  chart-pullback is analytic (so `ωᵢ − ωⱼ ∈ Ω`, the `δμ ∈ Z¹(Ω)` condition); this is what makes the
  per-pole residue patch-independent.
* `holoOff` — off the poles, each `gᵢ`'s chart-pullback is analytic at every point of `Uᵢ` (so `ωᵢ` is
  holomorphic away from the recorded poles).
* `iso` — at each pole `a`, `ω₀·g_{patch a}` has an isolated singularity (so the local residue is the
  honest contour-computable Laurent residue). -/
structure GeneralMLDistribution (ω₀ : HolomorphicOneForms X) where
  /-- The (finite) cover index. -/
  ι : Type
  /-- Finiteness of the index. -/
  [fintype : Fintype ι]
  /-- The cover opens. -/
  U : ι → Opens X
  /-- The local principal-part function on each patch (`ωᵢ = gᵢ·ω₀`). -/
  g : ι → (X → ℂ)
  /-- The finite pole set. -/
  poles : Finset X
  /-- A designated patch containing each pole. -/
  patch : X → ι
  /-- Each pole lies in its designated patch. -/
  patch_mem : ∀ a ∈ poles, a ∈ U (patch a)
  /-- **Holomorphic-difference condition** (`δμ ∈ Z¹(Ω)`): on every overlap the difference of two
  local principal parts is chart-analytic. -/
  holoDiff : ∀ (i j : ι) (a : X), a ∈ U i → a ∈ U j →
    AnalyticAt ℂ (fun z => (g i - g j) ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)
  /-- **Off-poles holomorphy**: away from the recorded poles each `gᵢ` is chart-analytic on its patch. -/
  holoOff : ∀ (i : ι) (a : X), a ∈ U i → a ∉ poles →
    AnalyticAt ℂ (fun z => g i ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)
  /-- **Isolated singularity** at each pole (in its designated patch). -/
  iso : ∀ a ∈ poles, formFnHoloPunctured ω₀ (g (patch a)) a

attribute [instance] GeneralMLDistribution.fintype

namespace GeneralMLDistribution

variable {ω₀ : HolomorphicOneForms X}

/-- **Each patch of a pole has an isolated singularity there.**  At a pole `a`, any patch `i ∋ a`
gives `ω₀·gᵢ` an isolated singularity: `gᵢ = (gᵢ − g_{patch a}) + g_{patch a}`, the first summand
analytic at `a` (`holoDiff`, both patches contain `a`) — hence isolated — and the second isolated
(`iso`); isolated-singularity is closed under addition (`formFnHoloPunctured`). -/
theorem formFnHoloPunctured_of_mem (μ : GeneralMLDistribution ω₀) {a : X} (ha : a ∈ μ.poles)
    {i : μ.ι} (hi : a ∈ μ.U i) :
    formFnHoloPunctured ω₀ (μ.g i) a := by
  -- The difference `gᵢ − g_{patch a}` is analytic at `a`, hence isolated.
  have hdiff : AnalyticAt ℂ (fun z => (μ.g i - μ.g (μ.patch a)) ((chartAt ℂ a).symm z))
      ((chartAt ℂ a) a) := μ.holoDiff i (μ.patch a) a hi (μ.patch_mem a ha)
  have hdiffiso : formFnHoloPunctured ω₀ (μ.g i - μ.g (μ.patch a)) a :=
    formFnHoloPunctured_of_analyticAt ω₀ _ a hdiff
  -- `gᵢ = (gᵢ − g_{patch a}) + g_{patch a}`, both summands isolated, so `gᵢ` is.
  have hsum : μ.g i = (μ.g i - μ.g (μ.patch a)) + μ.g (μ.patch a) := by
    ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hsum]
  -- `formFnHoloPunctured` of a sum from `formFnResidue_add`'s hypothesis pattern: both summands have
  -- isolated singularities, so their product integrands add, staying holomorphic on a punctured ball.
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := hdiffiso
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := μ.iso a ha
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun z hz => ?_⟩
  have hz1 : z ∈ ball ((chartAt ℂ a) a) ρ₁ \ {(chartAt ℂ a) a} :=
    ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩
  have hz2 : z ∈ ball ((chartAt ℂ a) a) ρ₂ \ {(chartAt ℂ a) a} :=
    ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩
  have heq : (fun z => coeffAt ω₀ a z * ((μ.g i - μ.g (μ.patch a)) + μ.g (μ.patch a))
        ((chartAt ℂ a).symm z))
      = (fun z => coeffAt ω₀ a z * (μ.g i - μ.g (μ.patch a)) ((chartAt ℂ a).symm z))
        + fun z => coeffAt ω₀ a z * μ.g (μ.patch a) ((chartAt ℂ a).symm z) := by
    funext w; simp only [Pi.add_apply]; ring
  rw [heq]; exact (hb₁ z hz1).add (hb₂ z hz2)

/-- **The per-pole residue** `Resₐ(μ) = Resₐ(ω₀·g_{patch a})` (Forster §17.2). -/
noncomputable def resAtPole (μ : GeneralMLDistribution ω₀) (a : X) : ℂ :=
  formFnResidue ω₀ (μ.g (μ.patch a)) a

/-- **Patch-independence of the per-pole residue** (Forster §17.2's well-definedness of `Resₐ(μ)`).
For a pole `a`, any patch `i` with `a ∈ Uᵢ` computes the same residue `Resₐ(ω₀·gᵢ) = Resₐ(μ)`: the
two local forms differ by a holomorphic form (`holoDiff`), which contributes residue `0`
(`formFnResidue_eq_of_analyticAt_sub`).  This is exactly Forster's "the difference `ωᵢ − ωⱼ` is
holomorphic and `ωᵢ`, `ωⱼ` have the same residue at `a`". -/
theorem resAtPole_eq_of_mem (μ : GeneralMLDistribution ω₀) {a : X} (ha : a ∈ μ.poles) {i : μ.ι}
    (hi : a ∈ μ.U i) :
    formFnResidue ω₀ (μ.g i) a = μ.resAtPole a := by
  -- `ω₀·gᵢ` has an isolated singularity at `a` (`formFnHoloPunctured_of_mem`), and `g i − g_{patch a}`
  -- is analytic at `a` (`holoDiff`, both patches contain `a`), so the two residues agree.
  have hdiff : AnalyticAt ℂ (fun z => (μ.g i - μ.g (μ.patch a)) ((chartAt ℂ a).symm z))
      ((chartAt ℂ a) a) := μ.holoDiff i (μ.patch a) a hi (μ.patch_mem a ha)
  exact formFnResidue_eq_of_analyticAt_sub ω₀ (μ.g i) (μ.g (μ.patch a)) a
    (μ.formFnHoloPunctured_of_mem ha hi) hdiff

/-- **Forster's residue `Res(μ)`** of a general Mittag–Leffler distribution: the sum of the per-pole
residues over the finite pole set.  This is the value of Forster's `Res` on the distribution; its
well-definedness on *cohomology classes* is the coboundary vanishing `res_eq_zero_of_globalMeromorphic`
(the `∑Res = 0` content). -/
noncomputable def res (μ : GeneralMLDistribution ω₀) : ℂ :=
  ∑ a ∈ μ.poles, μ.resAtPole a

theorem res_def (μ : GeneralMLDistribution ω₀) : μ.res = ∑ a ∈ μ.poles, μ.resAtPole a := rfl

/-! ### The coboundary vanishing `res = 0` (Forster §17.3, the `∑Res = 0` content)

The well-definedness of the global residue on *cohomology classes* (Forster §17.3) rests on: a
distribution that is *globally meromorphic* (all its local parts come from a single global meromorphic
function `f`, i.e. it is a coboundary `δμ = 0` in `H¹(X,Ω)`) has total residue `0`.  This is exactly
the **1-form residue theorem `∑Res = 0`** (`FormResidueTheorem`, Gate A).  We derive it for a
`GeneralMLDistribution` whose every local part agrees, near each pole, with a fixed global `f`. -/

/-- **The coboundary vanishing `res = 0`** (Forster §17.3, via the 1-form residue theorem `∑Res = 0`).
If a general Mittag–Leffler distribution `μ` is *globally meromorphic* — every local part `gᵢ` agrees
with a fixed global meromorphic function `f` near each pole in its patch (`hloc`: `gᵢ − f.toFun` is
chart-analytic at each pole `a ∈ Uᵢ`) — and the recorded pole set is the residue-theorem trace's pole
set (`hpoles`), then the total residue vanishes:

> `μ.res = ∑ₐ Resₐ(μ) = ∑ₐ Resₐ(ω₀·f) = residueSum ω₀ f.toFun (poles) = 0`.

The first equality is `resAtPole_eq_of_mem` + the local agreement (the residue is patch-independent
and, near each pole, `gᵢ` and `f` share their principal part, so `Resₐ(μ) = Resₐ(ω₀·f)`); the last is
the residue theorem `residueSum_eq_zero_of_formResidueTrace'` (`FormResidueTheorem`, the manifold
trace residue theorem — Gate A).  This is the precise statement `CousinResidueData.vanish_coboundary`
consumes: a *coboundary* class has zero residue, so the residue descends to `cechH1`. -/
theorem res_eq_zero_of_globalMeromorphic (μ : GeneralMLDistribution ω₀)
    (f : MeromorphicFunction X)
    (hloc : ∀ a ∈ μ.poles, AnalyticAt ℂ (fun z => (μ.g (μ.patch a) - f.toFun) ((chartAt ℂ a).symm z))
      ((chartAt ℂ a) a))
    (T : Jacobians.Dolbeault.FormResidueTheorem.FormResidueTrace ω₀ f.toFun)
    (hpoles : μ.poles = T.poles) :
    μ.res = 0 := by
  -- Each per-pole residue reads the global `f`'s residue (the local parts share `f`'s principal part).
  have hpole : ∀ a ∈ μ.poles, μ.resAtPole a = formFnResidue ω₀ f.toFun a := by
    intro a ha
    -- `Resₐ(μ) = Resₐ(ω₀·g_{patch a}) = Resₐ(ω₀·f)` since `g_{patch a} − f` is analytic at `a`.
    have hiso : formFnHoloPunctured ω₀ (μ.g (μ.patch a)) a :=
      μ.formFnHoloPunctured_of_mem ha (μ.patch_mem a ha)
    show formFnResidue ω₀ (μ.g (μ.patch a)) a = formFnResidue ω₀ f.toFun a
    exact formFnResidue_eq_of_analyticAt_sub ω₀ (μ.g (μ.patch a)) f.toFun a hiso (hloc a ha)
  -- So `μ.res = ∑ a ∈ poles, formFnResidue ω₀ f.toFun a = residueSum ω₀ f.toFun poles = 0`.
  rw [res_def, Finset.sum_congr rfl hpole]
  rw [show (∑ a ∈ μ.poles, formFnResidue ω₀ f.toFun a) = residueSum ω₀ f.toFun μ.poles from rfl,
    hpoles]
  exact Jacobians.Dolbeault.FormResidueTheorem.residueSum_eq_zero_of_formResidueTrace' ω₀ f.toFun T

/-! ### Non-vacuity: the single-`α·g` `MittagLefflerForm` is a general distribution

Embedding the existing `MittagLefflerForm` (one global `g`, the holomorphic case included) as a
one-patch `GeneralMLDistribution` confirms the general structure is **inhabited** at genuine data
(any number of poles), not a disguised `False`. -/

/-- The single-patch (`ι = Unit`, `U = X = ⊤`) general distribution from a `MittagLefflerForm μ`: one
global principal part `μ.g`, the same pole set, the trivial patch.  Its holomorphic-difference is
trivial (`g − g = 0` is analytic) and off-poles holomorphy / isolated-singularity are exactly `μ.holo`
/ `μ.iso`.  This shows the general structure subsumes the `α·g` shape. -/
def ofMittagLefflerForm (μ : MittagLefflerForm X) : GeneralMLDistribution μ.α where
  ι := Unit
  U := fun _ => ⊤
  g := fun _ => μ.g
  poles := μ.poles
  patch := fun _ => ()
  patch_mem := fun _ _ => trivial
  holoDiff := fun _ _ a _ _ => by
    simpa only [sub_self] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ))
      ((chartAt ℂ a) a))
  holoOff := fun _ a _ ha => μ.holo a ha
  iso := fun a ha => μ.iso a ha

@[simp] theorem ofMittagLefflerForm_resAtPole (μ : MittagLefflerForm X) (a : X) :
    (ofMittagLefflerForm μ).resAtPole a = formFnResidue μ.α μ.g a := rfl

/-- The embedded distribution has the **same total residue** as the `MittagLefflerForm`: both are
`∑ a ∈ poles, formFnResidue α g a`. -/
theorem res_ofMittagLefflerForm (μ : MittagLefflerForm X) :
    (ofMittagLefflerForm μ).res = μ.res := by
  rw [res_def, MittagLefflerForm.res, residueSum]
  exact Finset.sum_congr rfl fun a _ => rfl

/-! ### Sanity check — the machinery reads the genuine `dz/z` residue `= 1`

The per-pole residue `resAtPole` reads `formFnResidue ω₀ (g_{patch a}) a`, the **genuine Laurent
contour residue** (`resAt`), not a smooth-junk value.  We confirm it computes the correct value on the
Forster §17.6 `dz/z` configuration: for `ω₀` with a nonzero coefficient at `a` there is a principal
part `g` (the `dz/z` witness) whose per-pole residue is **`1 ≠ 0`** — exactly Forster's `Res(dz/z) = 1`,
the non-degeneracy heart.  This is the `ℂℙ¹`-style sanity check that the residue machinery is correct
(the residue genuinely sees the meromorphic singular part). -/

/-- **Sanity / non-degeneracy heart: the residue machinery reads the genuine `dz/z` residue `= 1`.**
At a point `a` where `α` has a nonzero coefficient, there is a principal-part function `g` such that
**any** general Mittag–Leffler distribution `μ` whose principal part at `a`'s designated patch is this
`g` has `resAtPole a = 1`.  Since `resAtPole a = formFnResidue α (μ.g (μ.patch a)) a` is the genuine
Laurent contour residue (`resAt`, not a smooth-junk value), this confirms the machinery computes the
**genuine** residue — and is exactly the Forster §17.6 `dz/z` residue-1 datum the non-degeneracy rests
on.  (`exists_formFnResidue_eq_one_of_localRep_ne_zero`, the `ℂℙ¹`-style sanity check.) -/
theorem exists_g_resAtPole_eq_one (α : HolomorphicOneForms X) {a : X}
    (ha : Jacobians.Montel.localRep α a a ≠ 0) :
    ∃ g : X → ℂ, ∀ μ : GeneralMLDistribution α, μ.g (μ.patch a) = g → μ.resAtPole a = 1 := by
  obtain ⟨g, hg⟩ := exists_formFnResidue_eq_one_of_localRep_ne_zero α a ha
  exact ⟨g, fun μ hμ => by rw [resAtPole, hμ]; exact hg⟩

end GeneralMLDistribution

end Jacobians.Dolbeault

end
