/-
  Riemann–Roch degree layer — the residue-theorem degree facts, split out of
  `RiemannRoch.lean` (base-file split, the proven Phase-C pattern; see
  `docs/planning/FLIP_CHECKLIST.md` §1.1).

  Why this file exists: the keystone flip re-pins `exists_riemannRoch_divisor`
  (`RiemannRoch.lean`) onto the unconditional ∃-cover keystone
  (`Dolbeault/KeystonePackaging.lean`), but `KeystonePackaging`'s import closure
  reached `RiemannRoch.lean` through `SerreDualityGenus0` / `TailSerre` /
  `SerreSurjectivitySkeleton` — which consume ONLY the two degree facts below.
  Moving them here (verbatim) and redirecting those three imports breaks the
  cycle with no statement changes.

  CONTENTS (moved verbatim from `RiemannRoch.lean`):
    • `MeromorphicFunction.deg_div` — every principal divisor has degree 0
      (Forster Cor. 4.25 / the argument principle, via the proven proper-map
      degree route).
    • `lDim_eq_zero_of_deg_neg` — `l(D) = 0` when `deg D < 0`.
-/
import KirovDolbeault.Abel
import KirovDolbeault.LinearSystem
import KirovDolbeault.MeromorphicLiouville
import KirovDolbeault.DegDivResidue
import KirovDolbeault.ProperMapDegreeSheets

-- Some declarations here are purely algebraic and use only `[ChartedSpace ℂ X]`,
-- not the full compact-manifold hypotheses carried by the consumers.
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Every principal divisor has degree `0` (Forster Cor. 4.25 / the argument principle). **PROVEN**
via the **degree route**: `deg (div f) = zerosCount f − polesCount f` (`deg_div_eq_zeros_sub_poles`),
and both counts equal a common proper-map degree `d` (`ProperMapDegreeSheets.exists_properMapDegree_proven`,
the §17.9 conservation-of-number construction — now axiom-clean), so the difference is `0`. The RR
derivations below consume this `deg_div`. (The old standalone `DegDivResidue.exists_properMapDegree`
that approach is now superseded by this proven route and no longer on any critical path.) -/
theorem MeromorphicFunction.deg_div (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := by
  obtain ⟨d, hz, hp⟩ := Jacobians.ProperMapDegreeSheets.exists_properMapDegree_proven f
  rw [deg_div_eq_zeros_sub_poles, hz, hp, sub_self]

/-- `l(D) = 0` when `deg D < 0`. Any `f ∈ L(D)` with nonzero germ would give (by faithfulness) a
divisor `div f ≥ −D` with `deg(div f) = 0 ≥ −deg D > 0`, impossible; so every `f ∈ L(D)` is germ-
zero, the quotient `L(D)/germZero` is trivial, and its dimension is `0`. -/
theorem lDim_eq_zero_of_deg_neg (D : Divisor X) (hD : Divisor.deg X D < 0) :
    lDim (X := X) D = 0 := by
  have hsub : linearSystem (X := X) D ≤ germZeroSubmodule := by
    intro f hf
    by_contra hng
    have hex : ∃ x₀, f.orderW x₀ ≠ ⊤ := by
      by_contra h; push Not at h; exact hng h
    have hfaith : ∀ z : X, f.orderW z ≠ ⊤ := fun z =>
      MeromorphicFunction.orderW_ne_top_of_exists f hex z
    have hdiv : ∀ x, -(D x) ≤ (f.div : Divisor X) x := by
      intro x
      have hmem : (-(D x) : WithTop ℤ) ≤ f.orderW x := hf x
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfaith x)
      rw [← hn] at hmem
      have hdivx : (f.div : Divisor X) x = n := by
        show (f.orderW x).untop₀ = n
        rw [← hn]; rfl
      rw [hdivx]; exact WithTop.coe_le_coe.mp hmem
    have heff : ∀ x, 0 ≤ (f.div + D) x := fun x => by
      rw [Finsupp.add_apply]; linarith [hdiv x]
    have hdeg_eff : (0 : ℤ) ≤ Divisor.deg X (f.div + D) := by
      change (0 : ℤ) ≤ ∑ i ∈ (f.div + D).support, (f.div + D) i
      exact Finset.sum_nonneg fun i _ => heff i
    rw [map_add, MeromorphicFunction.deg_div f] at hdeg_eff
    omega
  rw [lDim]
  have htop : (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D) = ⊤ :=
    Submodule.comap_subtype_eq_top.mpr hsub
  rw [htop]
  haveI : Subsingleton (↥(linearSystem (X := X) D) ⧸
      (⊤ : Submodule ℂ ↥(linearSystem (X := X) D))) :=
    ⟨fun a b => Quotient.inductionOn₂' a b fun x y =>
      (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top⟩
  exact Module.finrank_zero_of_subsingleton

end Jacobians
