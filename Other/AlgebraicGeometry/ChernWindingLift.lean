/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Logarithmic increments of a nonvanishing continuous function on a simply connected space

This file is the analytic-topological bottom layer of the winding homomorphism of
`Other/AlgebraicGeometry/ChernLocalModelWinding.lean`.

On a simply connected, locally path connected space `A` every continuous nowhere vanishing
`g : A → ℂ` is `exp ∘ L` for a continuous `L : A → ℂ`, unique once its value at one point is
prescribed (`Complex.isCoveringMapOn_exp` and Mathlib's lifting criterion).  The *difference*
`L b - L a` does not depend on the chosen lift: this is `ChernWinding.logIncrement`, the
(`2πi`-times) logarithmic increment of `g` from `a` to `b`.  It is

* additive in the two points (`logIncrement_add_logIncrement`),
* additive in `g` under multiplication (`logIncrement_mul`),
* natural in `A` (`logIncrement_comp`), and
* equal to the honest difference `f b - f a` when `g = exp ∘ f` (`logIncrement_of_exp`).

These four facts are exactly what makes `σ ↦ logIncrement (g ∘ σ) v₀ v₁` a singular `1`-cocycle
on any space, additive in `g` and a coboundary when `g` has a global logarithm; that cocycle is
the winding number, and it is built in `ChernWindingCochain.lean`.

The file also supplies the instances needed to apply the lifting criterion to the standard
topological simplices: a convex subset of a real topological vector space is locally path
connected (`ChernWinding.Convex.locallyPathConnectedSpace`) and, when nonempty, contractible,
hence simply connected.
-/

@[expose] public noncomputable section

open scoped unitInterval

namespace ChernWinding

/-! ### Convex subsets are locally path connected -/

section Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

/-- Inside a convex set, the preimage of a convex set containing a given point is path
connected. -/
theorem isPathConnected_preimage_of_convex (hs : Convex ℝ s) {t : Set E} (ht : Convex ℝ t)
    (x : s) (hx : (x : E) ∈ t) :
    IsPathConnected (Subtype.val ⁻¹' t : Set s) := by
  refine ⟨x, hx, fun y hy => ?_⟩
  refine ⟨⟨⟨fun τ => ⟨(1 - (τ : ℝ)) • (x : E) + (τ : ℝ) • (y : E),
      hs x.2 y.2 (by simpa using τ.2.2) τ.2.1 (by ring)⟩, by fun_prop⟩, ?_, ?_⟩, fun τ => ?_⟩
  · ext; simp
  · ext; simp
  · exact ht hx hy (by simpa using τ.2.2) τ.2.1 (by ring)

/-- A convex subset of a real normed space is locally path connected. -/
theorem Convex.locallyPathConnectedSpace (hs : Convex ℝ s) :
    LocallyPathConnectedSpace s := by
  refine LocallyPathConnectedSpace.of_bases (p := fun _ r => 0 < r)
    (s := fun x r => Metric.ball x r) (fun _ => Metric.nhds_basis_ball) fun x r hr => ?_
  have hball : (Metric.ball x r : Set s) = Subtype.val ⁻¹' Metric.ball (x : E) r := by
    ext y; simp [Metric.mem_ball, Subtype.dist_eq]
  rw [hball]
  exact isPathConnected_preimage_of_convex hs (convex_ball _ _) x (Metric.mem_ball_self hr)

end Convex

/-! ### Existence and rigidity of the exponential lift -/

variable {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]

/-- A continuous nowhere vanishing function on a simply connected, locally path connected space
has a continuous logarithm with any prescribed value at any prescribed point. -/
theorem existsUnique_expLift (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (a₀ : A) {e₀ : ℂ}
    (he : Complex.exp e₀ = g a₀) :
    ∃! L : C(A, ℂ), L a₀ = e₀ ∧ Complex.exp ∘ L = g :=
  Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g he fun a => hg a

/-- A continuous nowhere vanishing function on a simply connected, locally path connected space
is an exponential. -/
theorem exists_expLift (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (a₀ : A) :
    ∃ L : C(A, ℂ), ∀ a, Complex.exp (L a) = g a := by
  obtain ⟨L, ⟨-, hL⟩, -⟩ := existsUnique_expLift g hg a₀ (Complex.exp_log (hg a₀))
  exact ⟨L, fun a => congrFun hL a⟩

/-- Two continuous logarithms of the same function differ by a constant: their increments
agree. -/
theorem sub_eq_sub_of_exp_eq (L L' : C(A, ℂ)) (h : ∀ a, Complex.exp (L a) = Complex.exp (L' a))
    (a b : A) : L b - L a = L' b - L' a := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h a)
  set c : ℂ := (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) with hc
  set M : C(A, ℂ) := ⟨fun x => L' x + c, by fun_prop⟩ with hM
  have hexpM : ∀ x, Complex.exp (M x) = Complex.exp (L x) := by
    intro x
    show Complex.exp (L' x + c) = Complex.exp (L x)
    rw [Complex.exp_add, hc, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact (h x).symm
  have hf : ∀ x, Complex.exp (L x) ≠ 0 := fun x => Complex.exp_ne_zero _
  obtain ⟨F, -, huniq⟩ :=
    existsUnique_expLift (A := A) ⟨fun x => Complex.exp (L x), by fun_prop⟩ hf a
      (e₀ := L a) rfl
  have h1 : L = F := huniq L ⟨rfl, rfl⟩
  have h2 : M = F := by
    refine huniq M ⟨?_, ?_⟩
    · simp [hM, hn]
    · funext x; exact hexpM x
  have hLM : L = M := h1.trans h2.symm
  rw [hLM]
  show L' b + c - (L' a + c) = L' b - L' a
  ring

/-- The logarithmic increment of a nowhere vanishing continuous function between two points of a
simply connected, locally path connected space: the difference of the values at those points of
any continuous logarithm. -/
def logIncrement (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (a b : A) : ℂ :=
  (exists_expLift g hg a).choose b - (exists_expLift g hg a).choose a

/-- The defining property: the increment is computed by any continuous logarithm. -/
theorem logIncrement_eq (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (L : C(A, ℂ))
    (hL : ∀ x, Complex.exp (L x) = g x) (a b : A) :
    logIncrement g hg a b = L b - L a :=
  sub_eq_sub_of_exp_eq _ L
    (fun x => ((exists_expLift g hg a).choose_spec x).trans (hL x).symm) a b

/-- The increment depends on the function only through its values. -/
theorem logIncrement_congr {g g' : C(A, ℂ)} (hg : ∀ a, g a ≠ 0) (hg' : ∀ a, g' a ≠ 0)
    (h : g = g') (a b : A) : logIncrement g hg a b = logIncrement g' hg' a b := by
  subst h; rfl

@[simp] theorem logIncrement_self (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (a : A) :
    logIncrement g hg a a = 0 := sub_self _

/-- The increment is additive in the endpoints. -/
theorem logIncrement_add_logIncrement (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (a b c : A) :
    logIncrement g hg a b + logIncrement g hg b c = logIncrement g hg a c := by
  obtain ⟨L, hL⟩ := exists_expLift g hg a
  rw [logIncrement_eq g hg L hL, logIncrement_eq g hg L hL, logIncrement_eq g hg L hL]
  ring

theorem logIncrement_symm (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (a b : A) :
    logIncrement g hg b a = -logIncrement g hg a b := by
  obtain ⟨L, hL⟩ := exists_expLift g hg a
  rw [logIncrement_eq g hg L hL, logIncrement_eq g hg L hL]
  ring

/-- The increment is additive in the function: the increment of a pointwise product is the sum
of the increments. -/
theorem logIncrement_mul (g h k : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (hh : ∀ a, h a ≠ 0)
    (hk : ∀ a, k a ≠ 0) (hmul : ∀ a, k a = g a * h a) (a b : A) :
    logIncrement k hk a b = logIncrement g hg a b + logIncrement h hh a b := by
  obtain ⟨L, hL⟩ := exists_expLift g hg a
  obtain ⟨N, hN⟩ := exists_expLift h hh a
  have hLN : ∀ x, Complex.exp ((⟨fun x => L x + N x, by fun_prop⟩ : C(A, ℂ)) x) = k x := by
    intro x
    show Complex.exp (L x + N x) = k x
    rw [Complex.exp_add, hL x, hN x, hmul x]
  rw [logIncrement_eq k hk _ hLN, logIncrement_eq g hg L hL, logIncrement_eq h hh N hN]
  show L b + N b - (L a + N a) = _
  ring

/-- A function with a global logarithm has the increments of that logarithm. -/
theorem logIncrement_of_exp (f : C(A, ℂ)) (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0)
    (hfg : ∀ a, Complex.exp (f a) = g a) (a b : A) :
    logIncrement g hg a b = f b - f a :=
  logIncrement_eq g hg f hfg a b

/-- **Integrality.**  If `g` takes the same value at the two endpoints — in particular along a
loop — the increment is an integer multiple of `2πi`.  This is the source of the integrality of
the winding number, and hence of the rationality of the winding periods. -/
theorem exists_int_logIncrement (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (a b : A) (hab : g a = g b) :
    ∃ n : ℤ, logIncrement g hg a b = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  obtain ⟨L, hL⟩ := exists_expLift g hg a
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hL b).trans (hab.symm.trans (hL a).symm))
  exact ⟨n, by rw [logIncrement_eq g hg L hL, hn]; ring⟩

/-- Naturality in the space. -/
theorem logIncrement_comp {A' : Type*} [TopologicalSpace A'] [SimplyConnectedSpace A']
    [LocallyPathConnectedSpace A'] (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0) (φ : C(A', A))
    (hgφ : ∀ a, (g.comp φ) a ≠ 0) (a b : A') :
    logIncrement (g.comp φ) hgφ a b = logIncrement g hg (φ a) (φ b) := by
  obtain ⟨L, hL⟩ := exists_expLift g hg (φ a)
  rw [logIncrement_eq (g.comp φ) hgφ (L.comp φ) (fun x => hL (φ x)),
    logIncrement_eq g hg L hL]
  rfl

end ChernWinding
