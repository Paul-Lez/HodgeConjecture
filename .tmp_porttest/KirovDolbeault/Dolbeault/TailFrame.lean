/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.LocalRealization
import KirovDolbeault.LinearSystem

/-!
# The Laurent-tail pairing frame (Miranda Ch. VI, rung 1)

The bottom rung of the Laurent-tail duality tower (route: Miranda, *Algebraic Curves and
Riemann Surfaces*, Ch. VI; `docs/planning/KIROV_ROUTE_IDEAS.md` items 3–4).  The frame is pure
Laurent-coefficient algebra over the already-landed limit-based coefficient
`laurentCoeff k F c` (`LocalRealization.lean`) — **no integration anywhere**.

* `MeromorphicFunction.tailCoeff f b k` — the order-`k` Laurent coefficient of a global
  meromorphic function at `b`, read in the ambient chart at `b` (exactly the chart `orderW`
  uses, so order bookkeeping is definitional).
* `laurentCoeff_shift` / `tailCoeff_eq_residue_monomial` — the **residue reading**: the `k`-th
  coefficient IS the order-`(−1)` coefficient (= the residue) of the product with the Miranda
  monomial tail `(z−c)^{−1−k}`.  This identifies coefficient extraction with the residue
  pairing of `f` against single-monomial Laurent tails.
* `tailCoeff_eq_zero_iff` / `tailCoeff_leading_ne_zero` — the kernel/detection laws inherited
  from `laurentCoeff_eq_zero_iff`: on `ord ≥ k` the coefficient vanishes iff `ord > k`, and at
  finite order `n` the leading coefficient is NONZERO.  The latter is the **single-monomial
  witness** of Miranda Lemma VI.3.6 (rung 2, `TailRegularity.lean`).
* `tailWindow lo hi` — the finite-dimensional space of formal Laurent tails supported in the
  order window `[lo, hi)` (`finrank = (hi − lo).toNat`), Miranda's truncated-tail space at one
  point in coefficient coordinates.
* `tailPairing f b` — the residue pairing of a formal tail against `f`:
  `q ↦ ∑ₖ q k · c_k(f at b)`, ℂ-linear in the tail, with
  `tailPairing f b (single k 1) = tailCoeff f b k`.

Everything here is point-local and chart-fixed (Miranda fixes a local coordinate per point once
and for all; we use the ambient chart at `b`).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace Dolbeault

/-! ## Part 0 — two one-variable supplements to the `laurentCoeff` API -/

/-- The coefficient of the zero function is `0` (the de-pole is identically `0`). -/
theorem laurentCoeff_zero_fun (k : ℤ) (c : ℂ) : laurentCoeff k (0 : ℂ → ℂ) c = 0 := by
  have hz : dePole k (0 : ℂ → ℂ) c = fun _ => (0 : ℂ) := by
    funext z
    simp [dePole]
  have ht : Tendsto (dePole k (0 : ℂ → ℂ) c) (𝓝[≠] c) (𝓝 0) := by
    rw [hz]
    exact tendsto_const_nhds
  rw [laurentCoeff, ht.limUnder_eq]

/-- **The residue reading of the order-`k` coefficient** (the Miranda monomial-tail shift):
`c_k(F) = c_{−1}((z−c)^{−1−k}·F)`, i.e. the `k`-th Laurent coefficient is the *residue* of the
product of `F` with the single-monomial tail `(z−c)^{−1−k}`.  Pointwise off `c` the two
de-poles agree (`(z−c)^{1}·(z−c)^{−1−k} = (z−c)^{−k}`), so the limits agree. -/
theorem laurentCoeff_shift (k : ℤ) (F : ℂ → ℂ) (c : ℂ) :
    laurentCoeff k F c
      = laurentCoeff (-1) (fun z => (z - c) ^ (-1 - k) * F z) c := by
  have heq : dePole (-1) (fun z => (z - c) ^ (-1 - k) * F z) c =ᶠ[𝓝[≠] c] dePole k F c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    simp only [dePole]
    rw [← mul_assoc, ← zpow_add₀ hzc, show -(-1 : ℤ) + (-1 - k) = -k from by ring]
  rw [laurentCoeff, laurentCoeff, limUnder, limUnder, Filter.map_congr heq.symm]

end Dolbeault

/-! ## Part 1 — the global tail coefficient `tailCoeff f b k` -/

namespace MeromorphicFunction

open Dolbeault

/-- **The order-`k` Laurent tail coefficient** of a global meromorphic function at `b ∈ X`,
read in the ambient chart at `b` — the same chart that defines `orderW`, so all order
bookkeeping below is definitional. -/
noncomputable def tailCoeff (f : MeromorphicFunction X) (b : X) (k : ℤ) : ℂ :=
  laurentCoeff k (f.toFun ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b)

/-- The chart read of `f` is meromorphic at the chart centre (the defining property). -/
theorem meromorphicAt_chartRead (f : MeromorphicFunction X) (b : X) :
    MeromorphicAt (f.toFun ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b) :=
  f.meromorphic b

/-- `orderW` IS the meromorphic order of the chart read (definitional). -/
theorem orderW_eq_chartRead (f : MeromorphicFunction X) (b : X) :
    f.orderW b
      = meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b) :=
  rfl

/-- **The kernel law** (Miranda VI.3.6's engine, one point, one order): on `ord ≥ k`, the
order-`k` tail coefficient vanishes iff the order is strictly larger. -/
theorem tailCoeff_eq_zero_iff (f : MeromorphicFunction X) (b : X) {k : ℤ}
    (hord : (k : WithTop ℤ) ≤ f.orderW b) :
    f.tailCoeff b k = 0 ↔ (k : WithTop ℤ) < f.orderW b :=
  laurentCoeff_eq_zero_iff (f.meromorphic b) hord

/-- **The single-monomial witness (detection direction)**: at finite order `n`, the leading
tail coefficient is NONZERO.  This is the nonvanishing that drives Miranda Lemma VI.3.6 — the
single monomial `(z−c)^{−1−n}` pairs `f` to its leading Laurent coefficient. -/
theorem tailCoeff_leading_ne_zero (f : MeromorphicFunction X) (b : X) {n : ℤ}
    (hn : f.orderW b = (n : WithTop ℤ)) :
    f.tailCoeff b n ≠ 0 := by
  intro hc
  have hlt := (f.tailCoeff_eq_zero_iff b (k := n) (le_of_eq hn.symm)).mp hc
  rw [hn] at hlt
  exact lt_irrefl _ hlt

/-- **The residue reading**: `tailCoeff f b k` is the order-`(−1)` coefficient — the residue —
of the chart read of `f` multiplied by the Miranda monomial tail `(z−c)^{−1−k}` at the chart
centre.  This is the single-monomial instance of the Laurent-tail residue pairing. -/
theorem tailCoeff_eq_residue_monomial (f : MeromorphicFunction X) (b : X) (k : ℤ) :
    f.tailCoeff b k
      = laurentCoeff (-1)
          (fun z => (z - (chartAt (H := ℂ) b) b) ^ (-1 - k)
            * (f.toFun ∘ (chartAt (H := ℂ) b).symm) z)
          ((chartAt (H := ℂ) b) b) :=
  laurentCoeff_shift k _ _

/-- `tailCoeff` is additive on the order-`≥ k` subspace. -/
theorem tailCoeff_add {f g : MeromorphicFunction X} {b : X} {k : ℤ}
    (hf : (k : WithTop ℤ) ≤ f.orderW b) (hg : (k : WithTop ℤ) ≤ g.orderW b) :
    (f + g).tailCoeff b k = f.tailCoeff b k + g.tailCoeff b k := by
  have hread : ((f + g).toFun ∘ (chartAt (H := ℂ) b).symm)
      = (f.toFun ∘ (chartAt (H := ℂ) b).symm) + (g.toFun ∘ (chartAt (H := ℂ) b).symm) := rfl
  rw [tailCoeff, hread]
  exact laurentCoeff_add (f.meromorphic b) (g.meromorphic b) hf hg

/-- `tailCoeff` is ℂ-homogeneous on the order-`≥ k` subspace. -/
theorem tailCoeff_smul (s : ℂ) {f : MeromorphicFunction X} {b : X} {k : ℤ}
    (hf : (k : WithTop ℤ) ≤ f.orderW b) :
    (s • f).tailCoeff b k = s * f.tailCoeff b k := by
  have hread : ((s • f).toFun ∘ (chartAt (H := ℂ) b).symm)
      = s • (f.toFun ∘ (chartAt (H := ℂ) b).symm) := rfl
  rw [tailCoeff, hread]
  exact laurentCoeff_smul s (f.meromorphic b) hf

/-- **Germ-zero junk does not move tail coefficients**: representatives of the same
`lSysModule` class have identical tail coefficients, so the tail pairing is well-defined on the
junk-free linear-system classes. -/
theorem tailCoeff_eq_of_sub_germZero {f f' : MeromorphicFunction X}
    (hd : f - f' ∈ germZeroSubmodule (X := X)) (b : X) (k : ℤ) :
    f.tailCoeff b k = f'.tailCoeff b k := by
  refine laurentCoeff_congr ?_
  have htop : meromorphicOrderAt
      ((f - f').toFun ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b) = ⊤ := hd b
  have hev : ((f - f').toFun ∘ (chartAt (H := ℂ) b).symm)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] 0 := meromorphicOrderAt_eq_top_iff.mp htop
  filter_upwards [hev] with z hz
  have hz' : f.toFun ((chartAt (H := ℂ) b).symm z)
      - f'.toFun ((chartAt (H := ℂ) b).symm z) = 0 := hz
  have : f.toFun ((chartAt (H := ℂ) b).symm z) = f'.toFun ((chartAt (H := ℂ) b).symm z) := by
    linear_combination hz'
  exact this

end MeromorphicFunction

namespace Dolbeault

/-! ## Part 2 — the finite-dimensional window tail space and the tail pairing -/

/-- **The window tail space**: formal Laurent tails (coefficient Finsupps over ℤ) supported in
the order window `[lo, hi)` — Miranda's one-point truncated-tail space `𝒯` in coefficient
coordinates (the formal tail `∑ₖ qₖ·z^k`, `lo ≤ k < hi`). -/
def tailWindow (lo hi : ℤ) : Submodule ℂ (ℤ →₀ ℂ) :=
  Finsupp.supported ℂ ℂ ↑(Finset.Ico lo hi)

/-- The single monomial `z^k` lies in every window containing `k`. -/
theorem single_mem_tailWindow {lo hi k : ℤ} (hlo : lo ≤ k) (hhi : k < hi) (a : ℂ) :
    Finsupp.single k a ∈ tailWindow lo hi :=
  Finsupp.single_mem_supported ℂ a (by simpa using ⟨hlo, hhi⟩)

instance tailWindow_finiteDimensional (lo hi : ℤ) :
    FiniteDimensional ℂ (tailWindow lo hi) :=
  (Finsupp.supportedEquivFinsupp (↑(Finset.Ico lo hi) : Set ℤ)).symm.finiteDimensional

/-- **The window tail space is finite-dimensional of dimension `hi − lo`** (the count of
admissible orders in `[lo, hi)`). -/
theorem finrank_tailWindow (lo hi : ℤ) :
    Module.finrank ℂ (tailWindow lo hi) = (hi - lo).toNat := by
  rw [tailWindow,
    (Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ)
      (↑(Finset.Ico lo hi) : Set ℤ)).finrank_eq,
    (Finsupp.linearEquivFunOnFinite ℂ ℂ _).finrank_eq, Module.finrank_pi]
  simp

/-- **The residue pairing of formal tails against a meromorphic function**: the ℂ-linear
functional `q ↦ ∑ₖ qₖ · c_k(f at b)` on formal tails.  By `tailCoeff_eq_residue_monomial`
each summand is the residue of `f` against the monomial tail `(z−c)^{−1−k}`, so this is the
finite Laurent-coefficient algebra form of the Serre residue pairing
`⟨f, t⟩ = Res_b(f·t·dz)`. -/
noncomputable def tailPairing (f : MeromorphicFunction X) (b : X) : (ℤ →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun k => LinearMap.toSpanSingleton ℂ ℂ (f.tailCoeff b k)

@[simp] theorem tailPairing_single (f : MeromorphicFunction X) (b : X) (k : ℤ) (a : ℂ) :
    tailPairing f b (Finsupp.single k a) = a * f.tailCoeff b k := by
  rw [tailPairing, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The pairing against the unit monomial tail is the tail coefficient itself — the
single-monomial witness in pairing form. -/
theorem tailPairing_single_one (f : MeromorphicFunction X) (b : X) (k : ℤ) :
    tailPairing f b (Finsupp.single k 1) = f.tailCoeff b k := by
  rw [tailPairing_single, one_mul]

end Dolbeault

end Jacobians

end
