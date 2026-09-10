/-
  Serre §17 — node 1 (gate D): existence of a nonconstant meromorphic function (`ω₀`-existence).

  This is the gate-D input to `exists_serreDualityData` (Forster §17 Serre duality). It supplies the
  raw analytic existence underlying the canonical divisor `K = div ω₀`: a NONCONSTANT meromorphic
  function `f` on the compact connected Riemann surface `X` (whence a nonzero meromorphic 1-form
  `ω₀ = df`).

  ## The argument (Serre-INDEPENDENT — no circularity)

  Everything rests on the now-PROVEN cohomological Riemann–Roch (χ-additivity, Forster §16),
  `Jacobians.Dolbeault.cohomological_riemannRoch`, which gives — for a locally-realizable cover `𝔘` —

      `(h⁰(D) : ℤ) − h¹(D) = deg D + 1 − h¹(0)`.

  Since `h¹(D) = h1Dim D ≥ 0`, this is an *inequality*

      `(h⁰(D) : ℤ) ≥ deg D + 1 − h¹(0)`.

  Take a point `P : X` (exists, `X` connected hence nonempty) and the effective divisor
  `D = (h¹(0) + 1) · P`. Then `deg D = h¹(0) + 1`, so `h⁰(D) ≥ 2`, i.e. `2 ≤ lDim D` (via the
  `h⁰ = l` bridge `h0Dim_eq_lDim`). A linear system of dimension `≥ 2` contains an element linearly
  independent from the class of the constant function `1`; such an element is a meromorphic function
  whose germ is NOT constant. That is the nonconstant witness.

  Crucially this uses `h¹(0) = h1Dim 0` — a FINITE number (the arithmetic kirovGenus
  `dim H¹(𝒪)`, finite by `finiteDimensional_cechH1_general`), **not** `kirovGenus X`. So it does **not**
  invoke `arithmeticGenus_eq_genus` / Serre duality: there is no circularity.

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §16 (the Riemann–Roch inequality
  `l(D) ≥ deg D + 1 − g` and its corollary that nonconstant meromorphic functions exist).
-/
import KirovDolbeault.Dolbeault.CohomologicalRR
import KirovDolbeault.Dolbeault.SkyscraperProductWitness
import KirovDolbeault.Dolbeault.CanonicalFormIso

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- `lSysModule` (= `L(D)/germZero`, with `lDim D = finrank ℂ (lSysModule D)`) is shared from
-- `Jacobians.Dolbeault.CanonicalFormIso` (a single definition, used by both the §17.4 isomorphism
-- layer and this gate-D node).

/-! ### The constant function `1` as a member of every effective linear system -/

/-- The constant meromorphic function `1` (order `0` everywhere). -/
noncomputable def constOneMero : MeromorphicFunction X :=
  ⟨fun _ => 1, fun _ => MeromorphicAt.const 1 _⟩

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem constOneMero_orderW (x : X) : (constOneMero (X := X)).orderW x = 0 := by
  show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
  rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (1 : ℂ)) from rfl,
    meromorphicOrderAt_const]
  simp

/-- The constant `1` lies in `L(D)` for any divisor `D` with all coefficients `≥ 0` (`0 ≤ D x`):
its order is `0 ≥ -(D x)`. -/
theorem constOneMero_mem_linearSystem {D : Divisor X} (hD : ∀ x, 0 ≤ D x) :
    constOneMero (X := X) ∈ linearSystem (X := X) D := by
  intro x
  rw [constOneMero_orderW x]
  have : (-(D x) : WithTop ℤ) ≤ 0 := by exact_mod_cast neg_nonpos.mpr (hD x)
  exact this

/-- The class of the constant `1` in the linear-system quotient `lSysModule D` is nonzero
(its order is `0 ≠ ⊤`, so it is not germ-zero). -/
theorem constOneMero_class_ne_zero {D : Divisor X} (hD : ∀ x, 0 ≤ D x) :
    (Submodule.Quotient.mk ⟨constOneMero (X := X), constOneMero_mem_linearSystem hD⟩ :
      lSysModule (X := X) D) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  intro hmem
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : (constOneMero (X := X)).orderW x = ⊤ := (Submodule.mem_comap.mp hmem) x
  rw [constOneMero_orderW x] at hx
  exact (by decide : (0 : WithTop ℤ) ≠ ⊤) hx

/-! ### The Riemann–Roch lower bound `2 ≤ lDim D` for a large effective divisor -/

/-- **Riemann–Roch inequality (Forster §16).** For a locally-realizable cover `𝔘` and any divisor
`D`, the cohomological RR equality gives, dropping the (nonnegative) `h¹(D)` term,

    `deg D + 1 − h¹(0) ≤ lDim D`.

(`h⁰(D) = lDim D` by `h0Dim_eq_lDim`; `h1Dim D ≥ 0` is `Int.natCast_nonneg`.) -/
theorem riemannRoch_inequality {𝔘 : FiniteCover X} (hR : 𝔘.LocallyRealizable) (D : Divisor X) :
    Divisor.deg X D + 1 - (𝔘.h1Dim 0 : ℤ) ≤ (lDim (X := X) D : ℤ) := by
  have hRR := cohomological_riemannRoch 𝔘 hR D
  rw [𝔘.h0Dim_eq_lDim D] at hRR
  have hnn : (0 : ℤ) ≤ (𝔘.h1Dim D : ℤ) := Int.natCast_nonneg _
  linarith

/-- **`2 ≤ lDim D` for `D = (h¹(0)+1)·P`.** Taking the effective divisor of degree `h¹(0)+1`
concentrated at a single point `P` makes the RR lower bound `deg D + 1 − h¹(0) = 2`. -/
theorem two_le_lDim_largeEffective {𝔘 : FiniteCover X} (hR : 𝔘.LocallyRealizable) (P : X) :
    2 ≤ lDim (X := X) (Finsupp.single P ((𝔘.h1Dim 0 : ℤ) + 1)) := by
  have hineq := riemannRoch_inequality hR (Finsupp.single P ((𝔘.h1Dim 0 : ℤ) + 1))
  rw [Divisor.deg_single] at hineq
  -- `deg D + 1 − h¹(0) = (h¹(0)+1) + 1 − h¹(0) = 2`.
  have h2 : (2 : ℤ) ≤ (lDim (X := X) (Finsupp.single P ((𝔘.h1Dim 0 : ℤ) + 1)) : ℤ) := by linarith
  exact_mod_cast h2

/-! ### Existence of a nonconstant meromorphic function (gate D) -/

/-- A meromorphic function `f` is **germ-constant** if it agrees, on a punctured neighbourhood of
every point, with one fixed scalar `c`. Negation of this is the working notion of "nonconstant"
(matching `germ_eq_const_of_mem_linearSystem_zero`, the Liouville statement). -/
def IsGermConstant (f : MeromorphicFunction X) : Prop :=
  ∃ c : ℂ, ∀ x, ∀ᶠ z in 𝓝[≠] x, f.toFun z = c

/-- **Gate D — existence of a nonconstant meromorphic function.**

On a compact connected Riemann surface `X` there is a NONCONSTANT meromorphic function: a
`f : MeromorphicFunction X` lying in some complete linear system `L(D)` whose germ is not constant
(`¬ IsGermConstant f`).

Proof: pick a point `P` and a locally-realizable (Leray) cover (`exists_realizableLerayCover`).
The Riemann–Roch inequality gives `2 ≤ lDim D` for `D = (h¹(0)+1)·P`
(`two_le_lDim_largeEffective`), so the quotient `lSysModule D` has finrank `≥ 2`. By
`exists_linearIndependent_pair_of_one_lt_finrank` applied to the nonzero class of the constant `1`,
there is a class `[g]` linearly independent from `[1]`. Its representative `g ∈ L(D)` cannot be
germ-constant: a germ-constant function in `L(D)` is germ-equal to `c·1`, hence `[g] = c·[1]`,
contradicting linear independence of `![[1], [g]]`. -/
theorem exists_nonconstant_meromorphic :
    ∃ (D : Divisor X) (f : MeromorphicFunction X),
      f ∈ linearSystem (X := X) D ∧ ¬ IsGermConstant f := by
  classical
  -- A point and a realizable Leray cover.
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  obtain ⟨𝔘, _hL, hR⟩ := exists_realizableLerayCover (X := X)
  set D : Divisor X := Finsupp.single P ((𝔘.h1Dim 0 : ℤ) + 1) with hDdef
  -- `D` is effective.
  have hDnn : ∀ x, 0 ≤ D x := by
    intro x
    rw [hDdef, Finsupp.single_apply]
    split <;> positivity
  refine ⟨D, ?_⟩
  -- The class of the constant `1` is nonzero in `lSysModule D`.
  set q1 : lSysModule (X := X) D :=
    Submodule.Quotient.mk ⟨constOneMero (X := X), constOneMero_mem_linearSystem hDnn⟩ with hq1
  have hq1_ne : q1 ≠ 0 := constOneMero_class_ne_zero hDnn
  -- `finrank ≥ 2`.
  have hfr : 1 < finrank ℂ (lSysModule (X := X) D) := by
    have h := two_le_lDim_largeEffective hR P
    rw [show lDim (X := X) D = finrank ℂ (lSysModule (X := X) D) from rfl] at h
    omega
  -- Get a class `y` linearly independent from `q1`.
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank hfr hq1_ne
  -- Lift `y` to a representative `g ∈ L(D)`.
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨(g : MeromorphicFunction X), g.2, ?_⟩
  -- Suppose `g` were germ-constant; derive a contradiction with linear independence.
  rintro ⟨c, hc⟩
  -- Then `[g] = c • [1]` in the quotient: `g − c·1` is germ-zero.
  have hgclass : (Submodule.Quotient.mk g : lSysModule (X := X) D) = c • q1 := by
    rw [hq1, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.submoduleOf,
      Submodule.mem_comap]
    intro x
    rw [MeromorphicFunction.orderW_eq_top_iff]
    filter_upwards [hc x] with z hz
    show ((g : MeromorphicFunction X) - c • constOneMero (X := X)).toFun z = 0
    simp only [MeromorphicFunction.sub_toFun, MeromorphicFunction.smul_toFun, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hz]
    show c - c * (1 : ℂ) = 0
    ring
  -- But `![q1, [g]]` linearly independent forbids `[g] = c • q1`.
  have hrel : c • q1 + (-1 : ℂ) • (Submodule.Quotient.mk g : lSysModule (X := X) D) = 0 := by
    rw [hgclass]; module
  exact one_ne_zero (neg_eq_zero.mp ((LinearIndependent.pair_iff.mp hy c (-1) hrel).2))

/-- **Gate D, headline form.** A compact connected Riemann surface carries a NONCONSTANT meromorphic
function (its germ is not constant). This is the existence underlying `ω₀ = df` — the nonzero
meromorphic 1-form whose canonical divisor `K = div ω₀` is the gate-D input to
`exists_serreDualityData`. A direct corollary of `exists_nonconstant_meromorphic`. -/
theorem exists_nonconstant_meromorphicFunction :
    ∃ f : MeromorphicFunction X, ¬ IsGermConstant f := by
  obtain ⟨_, f, _, hf⟩ := exists_nonconstant_meromorphic (X := X)
  exact ⟨f, hf⟩

end Jacobians.Dolbeault
