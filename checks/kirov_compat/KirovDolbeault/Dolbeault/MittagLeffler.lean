/-
  Mittag–Leffler distributions of 1-forms and the global residue `Res` (Forster §17.1–17.2).

  The PDE-free Serre route defines the residue functional
  `Res : H¹(X,Ω) → ℂ` via **Mittag–Leffler distributions**: a cochain `(ωᵢ)` of *local* meromorphic
  1-forms over a finite cover, with *holomorphic differences* `ωᵢ − ωⱼ` on overlaps, has only finitely
  many poles, and `Res(μ) = ∑_a Res_a(μ)` is the sum of the local Laurent residues over those poles.

  This file builds the **complete local pieces** of that construction — everything *except* the
  global well-definedness on cohomology classes, which needs the **1-form** residue theorem `∑Res = 0`
  (a separate node — the trace-to-ℙ¹ route, NOT `deg_div`; see the ⚠ correction below) and so is stated
  here only as a precise plan in the module docstring, never as a tactic gap.

  Concretely it provides:
    * `formFnHoloPunctured` — the "isolated singularity" predicate at a pole for `α·g` (the integrand
      `coeffAt α a · (g ∘ chart.symm)` is holomorphic on a punctured chart-ball), under which the local
      residue `formFnResidue α g a` is additive / ℂ-homogeneous / contour-independent.
    * `formFnResidue_add` / `formFnResidue_smul` — local ℂ-linearity of `Res_a(α·g)` in `g`.
    * `residueSum α g S` = `∑_{a ∈ S} formFnResidue α g a` — the finite residue-sum over a pole set
      `S : Finset X`, with:
        - `residueSum_add` / `residueSum_smul` — ℂ-linearity in `g` (over a common pole set);
        - `residueSum_eq_zero_of_analyticAt` — the **`Res(holomorphic) = 0`** vanishing (Forster's
          holomorphic-difference property: a holomorphic distribution has zero residue);
        - `residueSum_subset` / `residueSum_insert_analyticAt` — enlarging the pole set by points where
          `α·g` is holomorphic does not change the sum (so `S` need only contain the *actual* poles).
    * `MittagLefflerForm` — the Mittag–Leffler distribution-of-1-forms structure (a finite pole set
      `poles`, local principal-part functions `g a`, the running global form `α`), and its
      `MittagLefflerForm.res` = `residueSum α g poles`, with `res_add`, `res_smul`, `res_holomorphic`.

  For the `D = 0` Serre pairing the relevant 1-forms are `ω·f` (a global holomorphic `ω :
  HolomorphicOneForms X` times a meromorphic function `f`); the residue contributions are exactly
  `formFnResidue ω f a`, so this finite residue-sum is the `Res` side of the pairing, modulo the
  `∑Res = 0` well-definedness (see the plan at the bottom of this docstring).

  ## What is deliberately NOT here (the `∑Res = 0` wall — precise plan)

  `Res` as a map on **cohomology classes** `H¹(X,Ω)` (not on cochain representatives) needs that
  `residueSum` is **independent of the Mittag–Leffler representative**, i.e. that a *coboundary* (a
  globally-holomorphic distribution `ωᵢ = α|_{Uᵢ}` for a single global meromorphic `α`) has total
  residue `0`. That is the **residue theorem** `∑_a Res_a(α) = 0` for a global meromorphic 1-form `α`
  on the compact `X`.

  ⚠ CORRECTION (2026-06-04, verified vs Forster §17 + Miranda §VIII.3): this is the **general 1-form**
  residue theorem, and it is **NOT `deg_div`**. `deg_div` (`∑ₓ ord_x f = 0` for a meromorphic *function*
  `f`) is only the special case `α = df/f`; the residues of a general `α = ω₀·f` are Laurent
  coefficients, not orders, so discharging `deg_div`/`exists_properMapDegree` does NOT give this. The
  correct PDE-free route is the **algebraic residue theorem via the trace to ℙ¹** (Miranda, *Algebraic
  Curves and Riemann Surfaces*, §VIII.3): `∑_{p∈X} Res_p α = ∑_{q∈ℙ¹} Res_q(Tr α) = 0` (partial fractions
  on ℙ¹), reusing the repo's `TraceForm`/`pushforwardForm` + the RR-gated branched cover `X → ℙ¹` + one
  new "residue-of-a-trace" lemma (Miranda Lemma 3.2). Forster §17.1/§17.3 instead defines `Res` by
  `(2πi)⁻¹∬_X` (manifold Stokes), which this repo avoids. So the class-level `Res : cechH1 𝔘 Ω → ℂ` is
  gated on **this trace residue theorem (a separate node), NOT on `deg_div`**, and is NOT built here.
  The plan: once `∑Res = 0` (the 1-form residue theorem) is available, descend `residueSum` through
  `cechH1`'s quotient (the cocycle→cochain representative gives a finite pole set; two representatives
  differ by a coboundary whose `residueSum` is `0` by the residue theorem), yielding the well-defined
  functional. Everything
  in *this* file is complete and axiom-clean and depends on no open lemma.
-/
import KirovDolbeault.Dolbeault.FormCoeff

open scoped Manifold ContDiff Topology
open Complex Metric Filter

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The local "isolated singularity" predicate for `α·g`

`formFnResidue α g a` is the residue at `a` of the meromorphic 1-form `α·g`, computed in the canonical
chart as `resAt (coeffAt α a · (g ∘ chart.symm)) (chart a)`.  The residue calculus (`resAt_add`,
`resAt_smul`, `resAt_eq_smul_circleIntegral`) is ℂ-linear / contour-independent precisely when the
integrand has an *isolated* singularity at the contour centre — `HoloPunctured` in `Residue.lean`.  We
package the corresponding condition on `α·g` here. -/

/-- `α·g` has an isolated singularity (or none) at `a`: its chart integrand
`z ↦ coeffAt α a z · g (chart.symm z)` is holomorphic on a punctured chart-ball around `chart a`.
This is exactly `HoloPunctured (integrand) (chart a)`, the hypothesis under which `formFnResidue α g a`
is additive / ℂ-homogeneous / contour-computable. -/
def formFnHoloPunctured (α : HolomorphicOneForms X) (g : X → ℂ) (a : X) : Prop :=
  HoloPunctured (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)

/-- If `g`'s chart-pullback is holomorphic *at* `a` then `α·g` is holomorphic there, in particular it
has an isolated singularity (`formFnHoloPunctured`). The bridge from "no pole" to the residue-calculus
hypothesis. -/
theorem formFnHoloPunctured_of_analyticAt (α : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hg : AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    formFnHoloPunctured α g a := by
  have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target :=
    (chartAt ℂ a).map_source (mem_chart_source ℂ a)
  have hprod : AnalyticAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a) :=
    (coeffAt_analyticAt α a hmem).mul hg
  have hev := hprod.eventually_analyticAt
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz.1)).differentiableAt⟩

/-! ### Local ℂ-linearity of `Res_a(α·g)` in `g` -/

/-- **`Res_a` is additive in the function `g`.**  If both `α·g₁` and `α·g₂` have isolated
singularities at `a`, then `Res_a(α·(g₁+g₂)) = Res_a(α·g₁) + Res_a(α·g₂)`.  (The chart integrand
distributes: `coeffAt α a z · (g₁+g₂)(…) = coeffAt α a z · g₁(…) + coeffAt α a z · g₂(…)`.) -/
theorem formFnResidue_add (α : HolomorphicOneForms X) (g₁ g₂ : X → ℂ) (a : X)
    (h₁ : formFnHoloPunctured α g₁ a) (h₂ : formFnHoloPunctured α g₂ a) :
    formFnResidue α (g₁ + g₂) a = formFnResidue α g₁ a + formFnResidue α g₂ a := by
  unfold formFnResidue
  have hsum : (fun z => coeffAt α a z * (g₁ + g₂) ((chartAt ℂ a).symm z))
      = (fun z => coeffAt α a z * g₁ ((chartAt ℂ a).symm z))
        + fun z => coeffAt α a z * g₂ ((chartAt ℂ a).symm z) := by
    funext z; simp only [Pi.add_apply]; ring
  rw [hsum, resAt_add h₁ h₂]

/-- **`Res_a` is ℂ-homogeneous in the function `g`.**  If `α·g` has an isolated singularity at `a`,
then `Res_a(α·(c • g)) = c · Res_a(α·g)`. -/
theorem formFnResidue_smul (α : HolomorphicOneForms X) (c : ℂ) (g : X → ℂ) (a : X)
    (h : formFnHoloPunctured α g a) :
    formFnResidue α (c • g) a = c • formFnResidue α g a := by
  unfold formFnResidue
  have hsmul : (fun z => coeffAt α a z * (c • g) ((chartAt ℂ a).symm z))
      = c • fun z => coeffAt α a z * g ((chartAt ℂ a).symm z) := by
    funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [hsmul, resAt_smul c h]

/-! ### The finite residue-sum over a pole set

`residueSum α g S = ∑_{a ∈ S} Res_a(α·g)`.  Forster's `Res(μ)` for a Mittag–Leffler distribution is
this sum over the finite pole set; for the `D = 0` Serre pairing `α·g = ω·f`.  Its ℂ-linearity in `g`
and vanishing on holomorphic data come termwise from `formFnResidue_add`/`_smul`/`_eq_zero`. -/

/-- The **residue-sum** `∑_{a ∈ S} Res_a(α·g)` of the 1-form `α·g` over a finite set `S : Finset X` of
candidate poles.  This is the `Res` of a Mittag–Leffler distribution (Forster §17.2); enlarging `S`
beyond the actual poles is harmless (`residueSum_subset`). -/
noncomputable def residueSum (α : HolomorphicOneForms X) (g : X → ℂ) (S : Finset X) : ℂ :=
  ∑ a ∈ S, formFnResidue α g a

@[simp] theorem residueSum_empty (α : HolomorphicOneForms X) (g : X → ℂ) :
    residueSum α g ∅ = 0 := by simp [residueSum]

open scoped Classical in
theorem residueSum_insert (α : HolomorphicOneForms X) (g : X → ℂ) {a : X} {S : Finset X}
    (ha : a ∉ S) :
    residueSum α g (insert a S) = formFnResidue α g a + residueSum α g S := by
  simp [residueSum, Finset.sum_insert ha]

/-- **Additivity of the residue-sum in `g`** over a common pole set `S`, provided `α·g₁` and `α·g₂`
have isolated singularities at every `a ∈ S`. -/
theorem residueSum_add (α : HolomorphicOneForms X) (g₁ g₂ : X → ℂ) (S : Finset X)
    (h₁ : ∀ a ∈ S, formFnHoloPunctured α g₁ a) (h₂ : ∀ a ∈ S, formFnHoloPunctured α g₂ a) :
    residueSum α (g₁ + g₂) S = residueSum α g₁ S + residueSum α g₂ S := by
  unfold residueSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a ha => formFnResidue_add α g₁ g₂ a (h₁ a ha) (h₂ a ha)

/-- **ℂ-homogeneity of the residue-sum in `g`** over a pole set `S`, provided `α·g` has an isolated
singularity at every `a ∈ S`. -/
theorem residueSum_smul (α : HolomorphicOneForms X) (c : ℂ) (g : X → ℂ) (S : Finset X)
    (h : ∀ a ∈ S, formFnHoloPunctured α g a) :
    residueSum α (c • g) S = c • residueSum α g S := by
  unfold residueSum
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun a ha => formFnResidue_smul α c g a (h a ha)

/-- **`Res(holomorphic) = 0` for the residue-sum.**  If `g`'s chart-pullback is holomorphic at every
`a ∈ S` (so `α·g` has no pole on `S`), the residue-sum vanishes — Forster's holomorphic-difference
property: a holomorphic Mittag–Leffler distribution contributes no residue. -/
theorem residueSum_eq_zero_of_analyticAt (α : HolomorphicOneForms X) (g : X → ℂ) (S : Finset X)
    (hg : ∀ a ∈ S, AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    residueSum α g S = 0 := by
  unfold residueSum
  refine Finset.sum_eq_zero fun a ha => ?_
  exact formFnResidue_eq_zero_of_analyticAt α g a (hg a ha)

open scoped Classical in
/-- **Enlarging the pole set by a holomorphic point is harmless.**  If `α·g` is holomorphic at `a`,
adding `a` to the pole set does not change the residue-sum.  Combined with `residueSum_empty`, this
lets one shrink any pole set to the *actual* poles. -/
theorem residueSum_insert_analyticAt (α : HolomorphicOneForms X) (g : X → ℂ) (a : X) (S : Finset X)
    (ha : AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    residueSum α g (insert a S) = residueSum α g S := by
  by_cases hmem : a ∈ S
  · rw [Finset.insert_eq_self.mpr hmem]
  · rw [residueSum_insert α g hmem, formFnResidue_eq_zero_of_analyticAt α g a ha, zero_add]

/-- **The residue-sum only sees the poles inside `S`.**  If every point of `S \ T` is a holomorphic
point of `α·g`, then summing over `S` agrees with summing over `T` (for `T ⊆ S`).  In particular `S`
may be replaced by the actual pole locus. -/
theorem residueSum_subset (α : HolomorphicOneForms X) (g : X → ℂ) {S T : Finset X} (hTS : T ⊆ S)
    (hg : ∀ a ∈ S, a ∉ T → AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    residueSum α g S = residueSum α g T := by
  classical
  unfold residueSum
  rw [← Finset.sum_subset hTS]
  intro a haS haT
  exact formFnResidue_eq_zero_of_analyticAt α g a (hg a haS haT)

/-! ### The Mittag–Leffler distribution-of-1-forms structure

A **Mittag–Leffler distribution of 1-forms** (Forster §17.2), in the form relevant to the `D = 0`
Serre pairing: a global holomorphic form `α` times a function `g` that is holomorphic off a finite
pole set `poles` and has an isolated singularity at each pole.  (Forster's general definition is a
cochain `(ωᵢ)` of *local* meromorphic forms with holomorphic differences; over a Leray cover that
cochain is equivalent to a single global `α·g` up to a globally-holomorphic — hence residue-free —
summand, so this `α·g` form captures the residue data, which is all `Res` depends on.)

`res μ := residueSum α g poles` is the total residue, and is the value of Forster's `Res` on the
distribution.  Its well-definedness on **cohomology classes** (independence of the representative) is
the **1-form** residue theorem `∑Res = 0` (the trace-to-ℙ¹ route, NOT `deg_div` — see the ⚠ correction
in the module docstring), NOT proved here. -/

/-- A Mittag–Leffler distribution of 1-forms of the shape `α·g` (Forster §17.2): the global
holomorphic form `α`, the principal-part function `g`, a finite pole set `poles`, the off-poles
holomorphy of `g`'s chart-pullback (`holo`), and the isolated-singularity condition at each pole
(`iso`, needed so the local residues are additive/contour-computable). -/
structure MittagLefflerForm (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The global holomorphic 1-form factor `α`. -/
  α : HolomorphicOneForms X
  /-- The principal-part function `g` (for the Serre pairing `α·g = ω·f`, this is the meromorphic
  function `f`). -/
  g : X → ℂ
  /-- The finite set of poles. -/
  poles : Finset X
  /-- Off the pole set, `g`'s chart-pullback is holomorphic (so `α·g` is holomorphic there). -/
  holo : ∀ a, a ∉ poles → AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)
  /-- At each pole, `α·g` has an isolated singularity. -/
  iso : ∀ a ∈ poles, formFnHoloPunctured α g a

namespace MittagLefflerForm

variable (μ : MittagLefflerForm X)

/-- **Forster's residue `Res(μ)`**: the sum of the local residues of `α·g` over the poles. -/
noncomputable def res : ℂ := residueSum μ.α μ.g μ.poles

theorem res_def : μ.res = residueSum μ.α μ.g μ.poles := rfl

/-- The residue is **invariant under enlarging the recorded pole set** by any finite set of
holomorphic points — `res` depends only on the actual poles, not on the bookkeeping set `poles`. -/
theorem res_eq_residueSum_of_subset {S : Finset X} (hpS : μ.poles ⊆ S)
    (hS : ∀ a ∈ S, a ∉ μ.poles →
      AnalyticAt ℂ (fun z => μ.g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    μ.res = residueSum μ.α μ.g S := by
  rw [res, residueSum_subset μ.α μ.g hpS hS]

/-- **`Res = 0` for a holomorphic distribution.**  If `g` is holomorphic *everywhere* (its
chart-pullback is analytic at every point — i.e. `α·g` is a genuine holomorphic 1-form, a coboundary
in Forster's terms), the residue vanishes.  This is the residue-side of the holomorphic-difference
property the well-definedness of `Res` rests on. -/
theorem res_holomorphic
    (hg : ∀ a : X, AnalyticAt ℂ (fun z => μ.g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    μ.res = 0 :=
  residueSum_eq_zero_of_analyticAt μ.α μ.g μ.poles fun a _ => hg a

/-- **ℂ-scaling of the distribution.**  Scaling the principal-part function `g` by `c` scales the
distribution; the pole set and singularity structure are unchanged (`c • g` is analytic / isolated
wherever `g` is). -/
noncomputable def smul (c : ℂ) : MittagLefflerForm X where
  α := μ.α
  g := c • μ.g
  poles := μ.poles
  holo := fun a ha => by
    have := μ.holo a ha
    simpa only [Pi.smul_apply, smul_eq_mul] using (analyticAt_const.mul this)
  iso := fun a ha => by
    have h := μ.iso a ha
    obtain ⟨ρ, hρ, hball⟩ := h
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    have hd := hball z hz
    have : (fun z => coeffAt μ.α a z * (c • μ.g) ((chartAt ℂ a).symm z))
        = (fun z => c * (coeffAt μ.α a z * μ.g ((chartAt ℂ a).symm z))) := by
      funext w; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact (hd.const_mul c)

@[simp] theorem smul_α (c : ℂ) : (μ.smul c).α = μ.α := rfl
@[simp] theorem smul_g (c : ℂ) : (μ.smul c).g = c • μ.g := rfl
@[simp] theorem smul_poles (c : ℂ) : (μ.smul c).poles = μ.poles := rfl

/-- **`Res(c·μ) = c·Res(μ)`.** -/
theorem res_smul (c : ℂ) : (μ.smul c).res = c • μ.res := by
  rw [res, res, smul_α, smul_g, smul_poles, residueSum_smul μ.α c μ.g μ.poles μ.iso]

/-! #### Additive combination of two distributions sharing the global form `α` -/

section Combine

open scoped Classical in
/-- On the union of the two pole sets, `α·g₁` has an isolated singularity at every point (it is one at
poles of `μ₁` by `μ₁.iso`, and holomorphic — hence isolated — at points outside `μ₁.poles` by
`μ₁.holo`). -/
theorem formFnHoloPunctured_left_on_union (μ₁ μ₂ : MittagLefflerForm X) (a : X)
    (_ha : a ∈ μ₁.poles ∪ μ₂.poles) :
    formFnHoloPunctured μ₁.α μ₁.g a := by
  by_cases h : a ∈ μ₁.poles
  · exact μ₁.iso a h
  · exact formFnHoloPunctured_of_analyticAt μ₁.α μ₁.g a (μ₁.holo a h)

open scoped Classical in
/-- Symmetric statement for `μ₂` (with `α` rewritten to the shared `μ₁.α`). -/
theorem formFnHoloPunctured_right_on_union (μ₁ μ₂ : MittagLefflerForm X) (hα : μ₁.α = μ₂.α) (a : X)
    (_ha : a ∈ μ₁.poles ∪ μ₂.poles) :
    formFnHoloPunctured μ₁.α μ₂.g a := by
  rw [hα]
  by_cases h : a ∈ μ₂.poles
  · exact μ₂.iso a h
  · exact formFnHoloPunctured_of_analyticAt μ₂.α μ₂.g a (μ₂.holo a h)

open scoped Classical in
/-- The **sum** of two Mittag–Leffler distributions sharing the same global holomorphic form `α`:
`g := g₁ + g₂`, with pole set the union.  (Outside the union both pullbacks are holomorphic, so the
sum is too; at each point of the union both factors have isolated singularities, so the sum does.) -/
noncomputable def combine (μ₁ μ₂ : MittagLefflerForm X) (hα : μ₁.α = μ₂.α) :
    MittagLefflerForm X where
  α := μ₁.α
  g := μ₁.g + μ₂.g
  poles := μ₁.poles ∪ μ₂.poles
  holo := fun a ha => by
    have ha1 : a ∉ μ₁.poles := fun h => ha (Finset.mem_union_left _ h)
    have ha2 : a ∉ μ₂.poles := fun h => ha (Finset.mem_union_right _ h)
    have h1 := μ₁.holo a ha1
    have h2 := μ₂.holo a ha2
    have heq : (fun z => (μ₁.g + μ₂.g) ((chartAt ℂ a).symm z))
        = (fun z => μ₁.g ((chartAt ℂ a).symm z)) + fun z => μ₂.g ((chartAt ℂ a).symm z) := by
      funext z; simp [Pi.add_apply]
    rw [heq]; exact h1.add h2
  iso := fun a ha => by
    have hL := formFnHoloPunctured_left_on_union μ₁ μ₂ a ha
    have hR := formFnHoloPunctured_right_on_union μ₁ μ₂ hα a ha
    obtain ⟨ρ₁, hρ₁, hb₁⟩ := hL
    obtain ⟨ρ₂, hρ₂, hb₂⟩ := hR
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun z hz => ?_⟩
    have hz1 : z ∈ ball ((chartAt ℂ a) a) ρ₁ \ {(chartAt ℂ a) a} :=
      ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩
    have hz2 : z ∈ ball ((chartAt ℂ a) a) ρ₂ \ {(chartAt ℂ a) a} :=
      ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩
    have hd1 := hb₁ z hz1
    have hd2 := hb₂ z hz2
    have heq : (fun z => coeffAt μ₁.α a z * (μ₁.g + μ₂.g) ((chartAt ℂ a).symm z))
        = (fun z => coeffAt μ₁.α a z * μ₁.g ((chartAt ℂ a).symm z))
          + fun z => coeffAt μ₁.α a z * μ₂.g ((chartAt ℂ a).symm z) := by
      funext w; simp only [Pi.add_apply]; ring
    rw [heq]; exact hd1.add hd2

@[simp] theorem combine_α (μ₁ μ₂ : MittagLefflerForm X) (hα : μ₁.α = μ₂.α) :
    (combine μ₁ μ₂ hα).α = μ₁.α := rfl
@[simp] theorem combine_g (μ₁ μ₂ : MittagLefflerForm X) (hα : μ₁.α = μ₂.α) :
    (combine μ₁ μ₂ hα).g = μ₁.g + μ₂.g := rfl

open scoped Classical in
@[simp] theorem combine_poles (μ₁ μ₂ : MittagLefflerForm X) (hα : μ₁.α = μ₂.α) :
    (combine μ₁ μ₂ hα).poles = μ₁.poles ∪ μ₂.poles := rfl

open scoped Classical in
/-- **`Res(μ₁ + μ₂) = Res(μ₁) + Res(μ₂)`** for distributions sharing the global form `α`.  The sum is
taken over the union pole set; each summand's residue-sum over the union agrees with its own via
`residueSum_subset` (the extra points are holomorphic for that summand). -/
theorem res_combine (μ₁ μ₂ : MittagLefflerForm X) (hα : μ₁.α = μ₂.α) :
    (combine μ₁ μ₂ hα).res = μ₁.res + μ₂.res := by
  rw [res, combine_α, combine_g, combine_poles]
  rw [residueSum_add μ₁.α μ₁.g μ₂.g (μ₁.poles ∪ μ₂.poles)
    (fun a ha => formFnHoloPunctured_left_on_union μ₁ μ₂ a ha)
    (fun a ha => formFnHoloPunctured_right_on_union μ₁ μ₂ hα a ha)]
  congr 1
  · rw [res]
    refine residueSum_subset μ₁.α μ₁.g Finset.subset_union_left (fun a _ ha1 => ?_)
    exact μ₁.holo a ha1
  · rw [res, hα]
    refine residueSum_subset μ₂.α μ₂.g Finset.subset_union_right (fun a _ ha2 => ?_)
    exact μ₂.holo a ha2

end Combine

end MittagLefflerForm

end Jacobians.Dolbeault
