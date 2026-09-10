/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerreUnwind
import KirovDolbeault.Dolbeault.FineResidue.DescentVanish

/-!
# §17.7 unwinding, detection form — the reduction of `UnwindRegularity` to a detecting class

`GlobalResidue.UnwindRegularity G D` (`SerreUnwind.lean`) demands: a level-`E` functional
`ι_E(v)` factoring through `H¹(𝒪_E) → H¹(𝒪_D)` forces `v ∈ L(K−D)`.  Contrapositively it is a
**detection** statement: for `v ∉ L(K−D)` there must be a test class `ξ ∈ ker(H¹(𝒪_E) → H¹(𝒪_D))`
with `ι_E(v)(ξ) ≠ 0` — then no factoring `lam` can exist (`lam` kills `incl ξ = 0` while the
pairing does not).  This file proves that reduction (`unwindRegularity_of_detects`, pure linear
algebra, valid for ANY `GlobalResidue`), plus the order bookkeeping locating the **forced bad
point** (`docs/planning/UNWIND_ROUTE.md`):

* `orderW_eq_of_sub_germZero` — germ-zero junk does not move `orderW`, so membership in
  `L(K−D)` is a property of the `lSysModule` class.
* `exists_lSysInclMono_eq_iff` — `mk f` is in the image of `L(K−D) → L(K−E)` iff `f` itself
  satisfies the `L(K−D)` order bounds.
* `exists_bad_point` — a class outside the image has a point `b` with FINITE order `n` and
  `E b − K b ≤ n < D b − K b`; in particular `E b < D b` (bad points are jump points).

The detecting class itself (the analytic half: the skyscraper test cocycle and its residue
evaluation through the R-lane engine) is built downstream for the concrete fine-sheaf residue.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), Lemma 17.7 (p. 137).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 0 — germ-zero junk does not move `orderW` -/

/-- `min`-bound for the order of a sum of meromorphic functions (the `linearSystem.add_mem'`
computation, exported). -/
theorem MeromorphicFunction.min_orderW_le_add (f g : MeromorphicFunction X) (x : X) :
    min (f.orderW x) (g.orderW x) ≤ (f + g).orderW x :=
  meromorphicOrderAt_add (f.meromorphic x) (g.meromorphic x)

/-- **Germ-zero differences do not move `orderW`**: if `f − f'` is a germ-zero junk function
(order `⊤` everywhere), then `f` and `f'` have the same order at every point. -/
theorem MeromorphicFunction.orderW_eq_of_sub_germZero {f f' : MeromorphicFunction X}
    (hd : f - f' ∈ germZeroSubmodule (X := X)) (x : X) :
    f.orderW x = f'.orderW x := by
  have hd' : f' - f ∈ germZeroSubmodule (X := X) := by
    have := neg_mem hd
    rwa [neg_sub] at this
  refine le_antisymm ?_ ?_
  · -- `f' = (f' − f) + f`, and the junk summand has order `⊤`
    have h1 := MeromorphicFunction.min_orderW_le_add (f' - f) f x
    rw [sub_add_cancel] at h1
    rw [hd' x, min_eq_right le_top] at h1
    exact h1
  · -- `f = (f − f') + f'`
    have h1 := MeromorphicFunction.min_orderW_le_add (f - f') f' x
    rw [sub_add_cancel] at h1
    rw [hd x, min_eq_right le_top] at h1
    exact h1

/-! ## Part 1 — the image of the monotone linear-system inclusion, order-theoretically -/

namespace Dolbeault

variable {K : Divisor X}

/-- **Image characterization of `lSysInclMono`**: the class of `f ∈ L(K−E)` lies in the image
of `L(K−D) → L(K−E)` (`E ≤ D`) iff `f` itself satisfies the `L(K−D)` order bounds.  (Junk-free:
germ-zero representatives have identical orders.) -/
theorem exists_lSysInclMono_eq_iff {E D : Divisor X} (hED : ∀ x, E x ≤ D x)
    (f : ↥(linearSystem (X := X) (K - E))) :
    (∃ u : lSysModule (X := X) (K - D),
        lSysInclMono (divisor_sub_le_sub_left K hED) u = Submodule.Quotient.mk f)
      ↔ (f : MeromorphicFunction X) ∈ linearSystem (X := X) (K - D) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨u₀, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [lSysInclMono_mk] at hu
    -- the difference of representatives is germ-zero
    have hdiff := (Submodule.Quotient.eq _).mp hu
    rw [Submodule.submoduleOf, Submodule.mem_comap] at hdiff
    have hdiff' : (u₀ : MeromorphicFunction X) - (f : MeromorphicFunction X)
        ∈ germZeroSubmodule (X := X) := hdiff
    intro x
    rw [← MeromorphicFunction.orderW_eq_of_sub_germZero hdiff' x]
    exact u₀.2 x
  · intro hf
    refine ⟨Submodule.Quotient.mk ⟨(f : MeromorphicFunction X), hf⟩, ?_⟩
    rw [lSysInclMono_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- **The forced bad point** (Forster 17.7's evaluation point): a level-`E` class outside the
image of `L(K−D)` has a point `b` where the order is FINITE, at least the `L(K−E)` bound, and
strictly below the `L(K−D)` bound.  In particular `E b < D b`: bad points are jump points of
`E ≤ D`. -/
theorem exists_bad_point {E D : Divisor X} (hED : ∀ x, E x ≤ D x)
    (f : ↥(linearSystem (X := X) (K - E)))
    (hno : ¬ ∃ u : lSysModule (X := X) (K - D),
        lSysInclMono (divisor_sub_le_sub_left K hED) u = Submodule.Quotient.mk f) :
    ∃ (b : X) (n : ℤ), (f : MeromorphicFunction X).orderW b = (n : WithTop ℤ) ∧
      E b - K b ≤ n ∧ n < D b - K b := by
  rw [exists_lSysInclMono_eq_iff hED f] at hno
  simp only [linearSystem, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, not_forall] at hno
  obtain ⟨b, hb⟩ := hno
  -- the failed bound: `ord < D b − K b` (note `−((K−D) b) = D b − K b`)
  have hKD : (-((K - D : Divisor X) b) : ℤ) = D b - K b := by
    rw [Finsupp.sub_apply]
    ring
  have hKE : (-((K - E : Divisor X) b) : ℤ) = E b - K b := by
    rw [Finsupp.sub_apply]
    ring
  have hlt : (f : MeromorphicFunction X).orderW b < ((D b - K b : ℤ) : WithTop ℤ) := by
    rw [← hKD]
    exact lt_of_not_ge hb
  have hge : ((E b - K b : ℤ) : WithTop ℤ) ≤ (f : MeromorphicFunction X).orderW b := by
    rw [← hKE]
    exact f.2 b
  -- the order is finite
  have hne : (f : MeromorphicFunction X).orderW b ≠ ⊤ := by
    intro hc
    rw [hc] at hlt
    exact (not_top_lt hlt)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨b, n, hn.symm, ?_, ?_⟩
  · rw [← hn] at hge
    exact_mod_cast hge
  · rw [← hn] at hlt
    exact_mod_cast hlt

/-! ## Part 2 — the detection reduction (pure linear algebra, any `GlobalResidue`) -/

namespace GlobalResidue

variable {𝔘 : FiniteCover X}

/-- **The detection reduction of Forster 17.7**: if every class outside the image of
`L(K−D) → L(K−E)` is DETECTED by some kernel class of `H¹(𝒪_E) → H¹(𝒪_D)` (nonzero pairing),
then `UnwindRegularity G D` holds.  A factoring `lam` would have to kill the detector
(`lam (incl ξ) = lam 0 = 0`) while the pairing does not — contradiction. -/
theorem unwindRegularity_of_detects (G : GlobalResidue 𝔘 K) (D : Divisor X)
    (hdet : ∀ (E : Divisor X) (hED : ∀ x, E x ≤ D x) (v : lSysModule (X := X) (K - E)),
      ¬ (∃ u : lSysModule (X := X) (K - D),
          lSysInclMono (divisor_sub_le_sub_left K hED) u = v) →
      ∃ ξ : 𝔘.cechH1 E, 𝔘.h1InclMono hED ξ = 0 ∧ (G.pairing E v) ξ ≠ 0) :
    G.UnwindRegularity D := by
  intro E hED v lam hfac
  by_contra hno
  obtain ⟨ξ, hker, hne⟩ := hdet E hED v hno
  apply hne
  have h1 := DFunLike.congr_fun hfac ξ
  rw [h1, LinearMap.comp_apply, hker, map_zero]

end GlobalResidue

/-! ## Part 3 — the skyscraper test cocycle at an isolated jump point

The detecting class for the concrete fine-sheaf residue: at an isolated jump point `b` with
level `E b ≤ m < D b`, the **exact-order local Mittag–Leffler witness** (proven for the
canonical chart-disk cover, `exists_orderExact_witness_chartDisk`) supplies a section
`γ ∈ 𝒪_{Ě+b}(U j₀)` (`Ě := E + (m − E b)·b`) of order exactly `−(m+1)` at `b`.  Its
`Pi.single` coboundary is a `Z¹(𝒪_E)` cocycle (overlaps avoid `b` by isolation, and the
`𝒪_{Ě+b}` bound IS the `𝒪_E` bound off `b` — the witness absorbs all `E`-negative zero
requirements), trivialized at level `D` by the cochain itself (`m + 1 ≤ D b`). -/

/-- Pointwise-monotone divisor comparison on an open: `𝒪_{D₁}(V) ≤ 𝒪_{D₂}(V)`. -/
theorem OmegaD_mono {D₁ D₂ : Divisor X} {V : Opens X} (h : ∀ x ∈ V, D₁ x ≤ D₂ x) :
    OmegaD (X := X) D₁ V ≤ OmegaD D₂ V := by
  rintro f ⟨hmer, hord⟩
  refine ⟨hmer, fun v => le_trans ?_ (hord v)⟩
  have e1 : (-(D₁ v.1) : WithTop ℤ) = ((-(D₁ v.1) : ℤ) : WithTop ℤ) := rfl
  have e2 : (-(D₂ v.1) : WithTop ℤ) = ((-(D₂ v.1) : ℤ) : WithTop ℤ) := rfl
  rw [e1, e2]
  exact_mod_cast neg_le_neg (h v.1 v.2)

/-- Germ-class version of `OmegaD_mono`. -/
theorem OmegaDGerm_mono {D₁ D₂ : Divisor X} {V : Opens X} (h : ∀ x ∈ V, D₁ x ≤ D₂ x) :
    OmegaDGerm (X := X) D₁ V ≤ OmegaDGerm D₂ V :=
  Submodule.map_mono (OmegaD_mono h)

/-- **The exact-order local Mittag–Leffler witness** on a chart-disk cover: at every cover set
`U j ∋ P` and divisor `D`, a section of `𝒪_{D+P}(U j)` of order EXACTLY `−D(P)−1` at `P`.
Strictly stronger than `LocallyRealizable` (which only asks for the top coefficient); proven
for the canonical cover by the factorized-rational product witness. -/
def ExactOrderWitness (𝔇 : ChartDiskCover X) : Prop :=
  ∀ (D : Divisor X) (j : 𝔇.toFiniteCover.ι) (P : X) (hP : P ∈ 𝔇.U j),
    ∃ γ : ↥(𝔇.U j) → ℂ, γ ∈ OmegaD (D + Finsupp.single P 1) (𝔇.U j) ∧
      ordU γ ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ)

/-- The canonical chart-disk cover has the exact-order witness
(`exists_orderExact_witness_chartDisk`, the factorized-rational product witness). -/
theorem exactOrderWitness_chartDiskCover [Nonempty X] :
    ExactOrderWitness (chartDiskCover (X := X)) := by
  intro D j P hP
  obtain ⟨γ, hmem, hord⟩ := exists_orderExact_witness_chartDisk D j P hP
  exact ⟨γ, hmem, hord⟩

section TestCocycle

variable {𝔇 : ChartDiskCover X} [DecidableEq 𝔇.toFiniteCover.ι]

/-- **The skyscraper test datum** at level `(E, b, m)`: a distinguished-chart section with pole
of order exactly `m+1` at `b` and the `𝒪_E` bounds everywhere else on `U j₀`
(`Ě := E + (m − E b)·b`, so `𝒪_{Ě + b}` is exactly that bound package). -/
structure TestCocycleData (𝔇 : ChartDiskCover X) (E : Divisor X) (j₀ : 𝔇.toFiniteCover.ι)
    (b : X) (hb : b ∈ (𝔇.U j₀ : Set X)) (m : ℤ) where
  /-- The distinguished-chart section. -/
  γ : ↥(𝔇.U j₀) → ℂ
  /-- `γ ∈ 𝒪_{Ě + b}(U j₀)` with `Ě := E + (m − E b)·b`. -/
  mem : γ ∈ OmegaD (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j₀)
  /-- The order at `b` is exactly `−(m+1)`. -/
  ord : ordU γ ⟨b, hb⟩ = ((-m - 1 : ℤ) : WithTop ℤ)

/-- The exact-order witness inhabits the test datum at every admissible level (`E b ≤ m`). -/
theorem TestCocycleData.exists_of_witness (hwit : ExactOrderWitness 𝔇) {E : Divisor X}
    {j₀ : 𝔇.toFiniteCover.ι} {b : X} (hb : b ∈ (𝔇.U j₀ : Set X)) {m : ℤ} (_hmE : E b ≤ m) :
    Nonempty (TestCocycleData 𝔇 E j₀ b hb m) := by
  obtain ⟨γ, hmem, hord⟩ := hwit (E + Finsupp.single b (m - E b)) j₀ b hb
  refine ⟨⟨γ, hmem, ?_⟩⟩
  rw [hord]
  congr 1
  have hEb : (E + Finsupp.single b (m - E b)) b = m := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    ring
  rw [hEb]

namespace TestCocycleData

variable {E D : Divisor X} {j₀ : 𝔇.toFiniteCover.ι} {b : X} {hb : b ∈ (𝔇.U j₀ : Set X)} {m : ℤ}

/-- The divisor bound carried by the test section, at the marked point. -/
private theorem divisor_apply_self :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) b = m + 1 := by
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_same]
  ring

/-- The divisor bound carried by the test section, away from the marked point. -/
private theorem divisor_apply_ne {x : X} (hx : x ≠ b) :
    (E + Finsupp.single b (m - E b) + Finsupp.single b 1 : Divisor X) x = E x := by
  rw [Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx,
    Finsupp.single_eq_of_ne (a := b) (a' := x) hx]
  ring

/-- The skyscraper test 0-cochain: the test germ on the distinguished set, `0` elsewhere. -/
noncomputable def cochain (td : TestCocycleData 𝔇 E j₀ b hb m) :
    𝔇.toFiniteCover.toFiniteFamily.Cochain0 :=
  Pi.single j₀ (toGerm (𝔇.U j₀) td.γ)

theorem cochain_self (td : TestCocycleData 𝔇 E j₀ b hb m) :
    td.cochain j₀ = toGerm (𝔇.U j₀) td.γ := by
  rw [cochain, Pi.single_eq_same]

theorem cochain_of_ne (td : TestCocycleData 𝔇 E j₀ b hb m) {j : 𝔇.toFiniteCover.ι}
    (hj : j ≠ j₀) : td.cochain j = 0 := by
  rw [cochain, Pi.single_eq_of_ne hj]

/-- **Level-`D` membership of the test cochain** (`m + 1 ≤ D b`, `E ≤ D`): the cochain whose
coboundary trivializes the test class in `H¹(𝒪_D)`. -/
theorem cochain_mem_sections0 (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hED : ∀ x, E x ≤ D x) (hmD : m + 1 ≤ D b) :
    td.cochain ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 D := by
  intro i
  by_cases hi : i = j₀
  · rw [hi, td.cochain_self]
    refine OmegaDGerm_mono (D₁ := E + Finsupp.single b (m - E b) + Finsupp.single b 1)
      (fun x _ => ?_) ⟨td.γ, td.mem, rfl⟩
    by_cases hx : x = b
    · rw [hx, divisor_apply_self]
      exact hmD
    · rw [divisor_apply_ne hx]
      exact hED x
  · rw [td.cochain_of_ne hi]
    exact Submodule.zero_mem _

/-- **Level-`E` membership of the test coboundary**: the overlap components avoid `b`
(isolation), where the `𝒪_{Ě+b}` bound is the `𝒪_E` bound. -/
theorem delta_mem_sections1 (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections1 E := by
  intro p
  obtain ⟨i, j⟩ := p
  have hδ : 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain (i, j)
      = rawRestrictG inf_le_right (td.cochain j) - rawRestrictG inf_le_left (td.cochain i) := by
    simp only [FiniteFamily.cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
  rw [hδ]
  by_cases hi : i = j₀ <;> by_cases hj : j = j₀
  · -- diagonal pair: the two restrictions agree (proof-irrelevant `≤`)
    rw [hi, hj]
    have heq : rawRestrictG (inf_le_right : (𝔇.U j₀ ⊓ 𝔇.U j₀ : Opens X) ≤ 𝔇.U j₀)
          (td.cochain j₀)
        = rawRestrictG (inf_le_left : (𝔇.U j₀ ⊓ 𝔇.U j₀ : Opens X) ≤ 𝔇.U j₀)
          (td.cochain j₀) := rfl
    rw [heq, sub_self]
    exact Submodule.zero_mem _
  · -- `i = j₀`, `j ≠ j₀`: the `−γ` side on an overlap avoiding `b`
    rw [hi, td.cochain_of_ne hj, map_zero, zero_sub]
    refine neg_mem ?_
    have h1 : rawRestrictG (inf_le_left : (𝔇.U j₀ ⊓ 𝔇.U j : Opens X) ≤ 𝔇.U j₀)
        (td.cochain j₀) ∈ OmegaDGerm
          (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U j₀ ⊓ 𝔇.U j) := by
      rw [td.cochain_self]
      exact rawRestrictG_omegaDGerm _ ⟨td.γ, td.mem, rfl⟩
    refine OmegaDGerm_mono (fun x hx => ?_) h1
    have hxb : x ≠ b := fun hc => hbiso.2 j hj (hc ▸ hx.2)
    rw [divisor_apply_ne hxb]
  · -- `i ≠ j₀`, `j = j₀`: the `+γ` side
    rw [hj, td.cochain_of_ne hi, map_zero, sub_zero]
    have h1 : rawRestrictG (inf_le_right : (𝔇.U i ⊓ 𝔇.U j₀ : Opens X) ≤ 𝔇.U j₀)
        (td.cochain j₀) ∈ OmegaDGerm
          (E + Finsupp.single b (m - E b) + Finsupp.single b 1) (𝔇.U i ⊓ 𝔇.U j₀) := by
      rw [td.cochain_self]
      exact rawRestrictG_omegaDGerm _ ⟨td.γ, td.mem, rfl⟩
    refine OmegaDGerm_mono (fun x hx => ?_) h1
    have hxb : x ≠ b := fun hc => hbiso.2 i hi (hc ▸ hx.1)
    rw [divisor_apply_ne hxb]
  · -- neither distinguished: `0 − 0`
    rw [td.cochain_of_ne hi, td.cochain_of_ne hj, map_zero, map_zero, sub_zero]
    exact Submodule.zero_mem _

/-- The test coboundary is a cocycle (`δ² = 0`). -/
theorem delta_mem_ker (td : TestCocycleData 𝔇 E j₀ b hb m) :
    𝔇.toFiniteCover.toFiniteFamily.cechDelta1
      (𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain) = 0 := by
  have h := DFunLike.congr_fun
    (𝔇.toFiniteCover.toFiniteFamily.cechDelta1_comp_cechDelta0) td.cochain
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

/-- **The test cocycle**, as an element of `Z¹(𝒪_E)`. -/
noncomputable def cocycle (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) :
    ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 E) :=
  ⟨𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain,
    Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr td.delta_mem_ker, td.delta_mem_sections1 hbiso⟩⟩

@[simp] theorem cocycle_coe (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) :
    (td.cocycle hbiso : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0 td.cochain := rfl

/-- **The test class dies in `H¹(𝒪_D)`**: the monotone inclusion sends it to the class of a
`B¹(𝒪_D)`-coboundary. -/
theorem h1InclMono_cocycle_eq_zero (td : TestCocycleData 𝔇 E j₀ b hb m)
    (hbiso : FineResidue.MLIsolated 𝔇 j₀ b) (hED : ∀ x, E x ≤ D x) (hmD : m + 1 ≤ D b) :
    𝔇.toFiniteCover.h1InclMono hED
      (Submodule.Quotient.mk (td.cocycle hbiso)) = 0 := by
  rw [𝔇.toFiniteCover.h1InclMono_mk, Submodule.Quotient.mk_eq_zero]
  rw [Submodule.submoduleOf, Submodule.mem_comap]
  exact ⟨td.cochain, td.cochain_mem_sections0 hED hmD, rfl⟩

end TestCocycleData

end TestCocycle

/-! ## Part 4 — the residue evaluation of the cup against the test class

`cup (mk f) [δ⁰n̂] = [δ⁰(f·n̂)]` (the cup commutes with `δ⁰`), a one-marked-point meromorphic
coboundary: the part `f·γ` has order exactly `n − (m+1) = −K b − 1` at `b` and `≥ −K` elsewhere
on `U j₀`, so against the `dz`-slot (exact zero order `K b` at `b`, `SlotExactK`) the
slot-product has a SIMPLE pole at `b` with residue `r ≠ 0` (minimal orders pair uniquely:
`ord = −1` exactly, then `meromorphicOrderAt_eq_int_iff` + `dslope`), while at the other bad
points (the K-points) it extends (the DescentVanish product-germ trick at level `K + b`).
The evaluation engine (`resFunctional_eq_neg_residue_of_mero_coboundary`) then gives
`resCocycle (cup-rep) = −r ≠ 0`. -/

section Evaluation

open FineResidue

variable {𝔇 : ChartDiskCover X} [Nonempty X] [DecidableEq 𝔇.toFiniteCover.ι] {K : Divisor X}

/-- **The exact-order slot hypothesis**: in every chart containing it, every point sees the
`dz`-slot factor as `(ζ−α)^{(K a).toNat}·(unit)` with a NONVANISHING unit — for the chart
coefficients of `ω₀` with `K = div ω₀ ≥ 0` this is the definition of the divisor of the form.
Strengthens `SlotMatchesK` (which allows the unit to vanish). -/
def SlotExactK (𝔇 : ChartDiskCover X) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (K : Divisor X) : Prop :=
  ∀ (a : X) (j : 𝔇.toFiniteCover.ι), a ∈ (𝔇.U j : Set X) →
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u (chartMap 𝔇 j a) ∧ u (chartMap 𝔇 j a) ≠ 0 ∧
      ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j a), g j ζ = (ζ - chartMap 𝔇 j a) ^ (K a).toNat * u ζ

theorem SlotMatchesK_of_exact {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hexact : SlotExactK 𝔇 g K) : SlotMatchesK 𝔇 g K := fun a _ j₀ hj₀ =>
  (hexact a j₀ hj₀).imp fun _ h => ⟨h.1, h.2.2⟩

/-- The marked divisor `K + b` agrees with `K` away from `b`. -/
private theorem Kb_apply_ne {b x : X} (hx : x ≠ b) :
    (K + Finsupp.single b 1 : Divisor X) x = K x := by
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (a := b) (a' := x) hx, add_zero]

private theorem Kb_apply_self {b : X} :
    (K + Finsupp.single b 1 : Divisor X) b = K b + 1 := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same]

/-- **Chart transfer of meromorphy and order** from the ambient chart at `b` to the cover's
center chart: the two reads differ by the analytic transition with nonvanishing derivative. -/
theorem centerRead_data {j₀ : 𝔇.toFiniteCover.ι} {b : X}
    (hb : b ∈ (𝔇.U j₀ : Set X)) (H : X → ℂ)
    (hH : MeromorphicAt (H ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b)) :
    MeromorphicAt (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ b) ∧
      meromorphicOrderAt (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ b)
        = meromorphicOrderAt (H ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b) := by
  have hbsrc : b ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hb
  have hbb : b ∈ (chartAt (H := ℂ) b).source := mem_chart_source ℂ b
  set σ : ℂ → ℂ := (chartAt (H := ℂ) b) ∘ (chartAt ℂ (𝔇.center j₀)).symm with hσdef
  have hσan : AnalyticAt ℂ σ (chartMap 𝔇 j₀ b) :=
    transition_analyticAt_of_mem (y := 𝔇.center j₀) (z := b) hbsrc hbb
  have hσd : deriv σ (chartMap 𝔇 j₀ b) ≠ 0 :=
    transition_deriv_ne_zero (y := 𝔇.center j₀) (z := b) hbsrc hbb
  have hli : (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ b) = b :=
    (chartAt ℂ (𝔇.center j₀)).left_inv hbsrc
  have hσpt : σ (chartMap 𝔇 j₀ b) = (chartAt (H := ℂ) b) b := by
    simp only [hσdef, Function.comp_apply, hli]
  have hzt : chartMap 𝔇 j₀ b ∈ (chartAt ℂ (𝔇.center j₀)).target :=
    (chartAt ℂ (𝔇.center j₀)).map_source hbsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j₀)).symm (chartMap 𝔇 j₀ b) :=
    (chartAt ℂ (𝔇.center j₀)).continuousAt_symm hzt
  have hmem : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 j₀ b),
      (chartAt ℂ (𝔇.center j₀)).symm ζ ∈ (chartAt (H := ℂ) b).source := by
    refine hcont.preimage_mem_nhds ?_
    rw [hli]
    exact (chartAt (H := ℂ) b).open_source.mem_nhds hbb
  have hev : (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ))
      =ᶠ[𝓝 (chartMap 𝔇 j₀ b)] ((H ∘ (chartAt (H := ℂ) b).symm) ∘ σ) := by
    filter_upwards [hmem] with ζ hζ
    show H ((chartAt ℂ (𝔇.center j₀)).symm ζ)
        = H ((chartAt (H := ℂ) b).symm (σ ζ))
    simp only [hσdef, Function.comp_apply]
    rw [(chartAt (H := ℂ) b).left_inv hζ]
  have hHσ : MeromorphicAt ((H ∘ (chartAt (H := ℂ) b).symm) ∘ σ) (chartMap 𝔇 j₀ b) := by
    refine MeromorphicAt.comp_analyticAt ?_ hσan
    rw [hσpt]
    exact hH
  constructor
  · exact hHσ.congr (hev.filter_mono nhdsWithin_le_nhds).symm
  · rw [meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds),
      meromorphicOrderAt_comp_of_deriv_ne_zero hσan hσd, hσpt]

/-- **`holoFn` reads back an honest representative on a punctured neighbourhood of a marked
boundary point `b ∉ W`**: if `𝓝[≠] b`-eventually points lie in `W`, and the zero-extension of
the representative `F` is meromorphic of FINITE order at `b` (ambient chart), then the analytic
representative agrees with `Gext F` eventually on `𝓝[≠] b`.  The finite-order normal form makes
`Gext F` junk-free (a continuous formula) on a punctured neighbourhood, so the limit-repair
recovers its values (`holoFn_eq_of_tendsto`).  This is the boundary-point complement of
`holoFn_eq_holoRep_of_chart_analyticAt`. -/
theorem holoFn_eventuallyEq_near_marked {W : Opens X} {gcls : MGerm W}
    (hgc : gcls ∈ OmegaDGerm (0 : Divisor X) W) {F : ↥W → ℂ}
    (hgF : toGerm W F = gcls) {b : X}
    (hWnear : ∀ᶠ x in 𝓝[≠] b, x ∈ W) {nF : ℤ}
    (hFmer : MeromorphicAt (Gext F ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b))
    (hFord : meromorphicOrderAt (Gext F ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b)
      = (nF : WithTop ℤ)) :
    ∀ᶠ x in 𝓝[≠] b, holoFn hgc x = Gext F x := by
  classical
  set ψ := chartAt (H := ℂ) b with hψdef
  set β := ψ b with hβdef
  have hbsrc : b ∈ ψ.source := mem_chart_source ℂ b
  -- the junk-free normal form on a punctured chart neighbourhood
  obtain ⟨w, hwan, hw0, hwe⟩ := (meromorphicOrderAt_eq_int_iff hFmer).mp hFord
  set φX : X → ℂ := fun y => (ψ y - β) ^ nF • w (ψ y) with hφXdef
  -- transfer the normal form to the X side
  have htendψ : Tendsto ψ (𝓝[≠] b) (𝓝[≠] β) := ψ.tendsto_nhdsNE hbsrc
  have hXside : ∀ᶠ x in 𝓝[≠] b, Gext F x = φX x := by
    have h1 : ∀ᶠ x in 𝓝[≠] b, (Gext F ∘ ψ.symm) (ψ x) = (ψ x - β) ^ nF • w (ψ x) :=
      htendψ.eventually hwe
    have h2 : ∀ᶠ x in 𝓝[≠] b, x ∈ ψ.source :=
      eventually_nhdsWithin_of_eventually_nhds (ψ.open_source.mem_nhds hbsrc)
    filter_upwards [h1, h2] with x hx1 hx2
    rw [Function.comp_apply, ψ.left_inv hx2] at hx1
    exact hx1
  -- the analyticity region of the unit factor, pulled back
  have hwana : ∀ᶠ x in 𝓝[≠] b, AnalyticAt ℂ w (ψ x) :=
    (htendψ.mono_right nhdsWithin_le_nhds).eventually hwan.eventually_analyticAt
  -- the open punctured neighbourhood carrying all four properties
  have hall : ∀ᶠ x in 𝓝[≠] b, x ∈ W ∧ x ∈ ψ.source ∧
      Gext F x = φX x ∧ AnalyticAt ℂ w (ψ x) := by
    filter_upwards [hWnear, eventually_nhdsWithin_of_eventually_nhds
      (ψ.open_source.mem_nhds hbsrc), hXside, hwana] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  rw [eventually_nhdsWithin_iff] at hall
  obtain ⟨O, hOp, hOopen, hbO⟩ := eventually_nhds_iff.mp hall
  -- pointwise: at each `x ∈ O ∖ {b}`, the limit-repair recovers `Gext F x`
  rw [eventually_nhdsWithin_iff]
  refine eventually_nhds_iff.mpr ⟨O, fun x hxO hxbne => ?_, hOopen, hbO⟩
  obtain ⟨hxW, hxsrc, hxval, hxw⟩ := hOp x hxO hxbne
  have hxb : x ≠ b := by simpa using hxbne
  -- the formula is continuous at `x`
  have hψne : ψ x ≠ β := fun hc => hxb (ψ.injOn hxsrc hbsrc hc)
  have hcψ : ContinuousAt ψ x := ψ.continuousAt hxsrc
  have hczpow : ContinuousAt (fun y => (ψ y - β) ^ nF) x := by
    have h1 : ContinuousAt (fun ζ : ℂ => (ζ - β) ^ nF) (ψ x) :=
      (continuousAt_id.sub continuousAt_const).zpow₀ nF (Or.inl (sub_ne_zero.mpr hψne))
    exact h1.comp hcψ
  have hcw : ContinuousAt (fun y => w (ψ y)) x := hxw.continuousAt.comp hcψ
  have hcont : ContinuousAt φX x := hczpow.smul hcw
  -- `Gext F` tends to its own value at `x` (it agrees with the formula near `x`)
  have hev : ∀ᶠ y in 𝓝 x, y ∈ O ∧ y ∈ ({b}ᶜ : Set X) := by
    filter_upwards [hOopen.mem_nhds hxO,
      isOpen_compl_singleton.mem_nhds (by simpa using hxb : x ∈ ({b}ᶜ : Set X))] with y h1 h2
    exact ⟨h1, h2⟩
  have htends : Tendsto (Gext F) (𝓝[≠] x) (𝓝 (Gext F x)) := by
    have h1 : Tendsto φX (𝓝[≠] x) (𝓝 (φX x)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [show Gext F x = φX x from hxval]
    refine h1.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev] with y hy
    exact ((hOp y hy.1 hy.2).2.2.1).symm
  exact holoFn_eq_of_tendsto hgc F hgF hxW htends

/-- **`SeparatesPoles` is stable under marking one cover-isolated point**: overlaps of distinct
cover sets avoid the isolated point, so the marked divisor `K + b` is still non-positive there. -/
theorem separatesPoles_add_single (hsep : SeparatesPoles 𝔇 K) {j₀ : 𝔇.toFiniteCover.ι} {b : X}
    (hbiso : MLIsolated 𝔇 j₀ b) :
    SeparatesPoles 𝔇 (K + Finsupp.single b 1) := by
  intro i j hij x hx
  have hxb : x ≠ b := by
    intro hc
    subst hc
    by_cases hi : i = j₀
    · exact hbiso.2 j (fun hj => hij (hi.trans hj.symm)) hx.2
    · exact hbiso.2 i hi hx.1
  rw [Kb_apply_ne hxb]
  exact hsep i j hij x hx

/-- **The marked-membership bookkeeping** (Forster 17.7's order count): `f ∈ L(K−E)` with exact
order `n = m − K b` at `b` lies in the shifted system `L((K+b) − (Ě+b))`,
`Ě := E + (m − E b)·b` — the exact membership the cup with the test cochain needs to land in
`𝒪_{K+b}`.  Off `b` the bound is the `L(K−E)` bound; at `b` it is `orderW f b ≥ n`, exact. -/
theorem mem_linearSystem_marked {E : Divisor X} {f : MeromorphicFunction X}
    (hfE : f ∈ linearSystem (X := X) (K - E)) {b : X} {n m : ℤ}
    (hn : f.orderW b = (n : WithTop ℤ)) (hm : m = n + K b) :
    f ∈ linearSystem (X := X)
      ((K + Finsupp.single b 1) - (E + Finsupp.single b (m - E b) + Finsupp.single b 1)) := by
  intro x
  by_cases hx : x = b
  · subst hx
    have h1 : ((K + Finsupp.single x 1
        - (E + Finsupp.single x (m - E x) + Finsupp.single x 1) : Divisor X)) x = -n := by
      simp only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    rw [h1, hn]
    have h2 : (- -n : ℤ) ≤ n := by omega
    exact_mod_cast h2
  · have hbx : b ≠ x := fun hc => hx hc.symm
    have h1 : ((K + Finsupp.single b 1
        - (E + Finsupp.single b (m - E b) + Finsupp.single b 1) : Divisor X)) x
        = (K - E : Divisor X) x := by
      simp only [Finsupp.sub_apply, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (a := b) (a' := x) hx]
      ring
    rw [h1]
    exact hfE x

namespace TestCocycleData

variable {E : Divisor X} {j₀ : 𝔇.toFiniteCover.ι} {b : X} {hb : b ∈ (𝔇.U j₀ : Set X)} {m : ℤ}

/-- **Level-`K+b` membership of the cup 0-cochain** `f · n̂`: the product of `f ∈ L(K−E)` (exact
order `n = m − K b` at `b`) with the skyscraper test cochain is a `sections0 (K+b)` cochain —
poles cancel against the linear-system bounds everywhere except the single marked simple
excess at `b`. -/
theorem cup_mem_sections0 (td : TestCocycleData 𝔇 E j₀ b hb m)
    {f : MeromorphicFunction X} (hfE : f ∈ linearSystem (X := X) (K - E))
    {n : ℤ} (hn : f.orderW b = (n : WithTop ℤ)) (hm : m = n + K b) :
    cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f td.cochain
      ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (K + Finsupp.single b 1) := by
  intro i
  by_cases hi : i = j₀
  · subst hi
    rw [cupCochain0_apply, td.cochain_self]
    exact mulConstG_omegaDGerm (mem_linearSystem_marked hfE hn hm) ⟨td.γ, td.mem, rfl⟩
  · rw [cupCochain0_apply, td.cochain_of_ne hi, mul_zero]
    exact Submodule.zero_mem _

/-- The honest product representative `(f∘val)·γ` of the marked cup component. -/
noncomputable def cupRep (td : TestCocycleData 𝔇 E j₀ b hb m) (f : MeromorphicFunction X) :
    ↥(𝔇.U j₀) → ℂ :=
  (f.toFun ∘ Subtype.val) * td.γ

/-- The product representative represents the marked cup-cochain component. -/
theorem toGerm_cupRep (td : TestCocycleData 𝔇 E j₀ b hb m) (f : MeromorphicFunction X) :
    toGerm (𝔇.U j₀) (td.cupRep f)
      = cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f td.cochain j₀ := by
  rw [cupCochain0_apply, td.cochain_self, globalGerm]
  rfl

/-- The product representative is meromorphic on the distinguished cover set. -/
theorem isMeromorphic_cupRep (td : TestCocycleData 𝔇 E j₀ b hb m) (f : MeromorphicFunction X) :
    IsMeromorphic ((𝔇.U j₀ : Opens X) : Type _) (td.cupRep f) :=
  fun u => ((isMeromorphic_val f) u).mul (td.mem.1 u)

/-- **The exact simple-excess order**: the product representative has order EXACTLY
`−K b − 1` at the marked point — `n` from the function, `−(m+1)` from the test section,
`m = n + K b`.  Order additivity is exact because both factor orders are finite. -/
theorem ordU_cupRep (td : TestCocycleData 𝔇 E j₀ b hb m) {f : MeromorphicFunction X}
    {n : ℤ} (hn : f.orderW b = (n : WithTop ℤ)) (hm : m = n + K b) :
    ordU (td.cupRep f) ⟨b, hb⟩ = ((-(K b) - 1 : ℤ) : WithTop ℤ) := by
  rw [cupRep, ordU_globalMul f td.mem.1 ⟨b, hb⟩, hn, td.ord]
  have hcast : ((n : ℤ) : WithTop ℤ) + ((-m - 1 : ℤ) : WithTop ℤ)
      = ((n + (-m - 1) : ℤ) : WithTop ℤ) := by
    norm_cast
  rw [hcast]
  congr 1
  omega

/-- **The marked simple pole of the slot-product** (the §17.7 evaluation core): the
off-`(K+b)`-points extraction of the cup 0-cochain `f·n̂`, read in the center chart and paired
against an exact-`K` slot, has a SIMPLE pole at the marked coordinate with NONZERO residue.
Orders are exact: `(−K b − 1) + K b = −1`, and order exactly `−1` forces a nonvanishing
leading coefficient. -/
theorem exists_slotProductSimplePoleAt (td : TestCocycleData 𝔇 E j₀ b hb m)
    {f : MeromorphicFunction X}
    {n : ℤ} (hn : f.orderW b = (n : WithTop ℤ)) (hm : m = n + K b) (hKb : 0 ≤ K b)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    {F0 : 𝔇.toFiniteCover.toFiniteFamily.Cochain0}
    (hF0 : F0 ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (K + Finsupp.single b 1))
    (hcomp : F0 j₀ = cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f td.cochain j₀) :
    ∃ r : ℂ, r ≠ 0 ∧ SlotProductSimplePoleAt 𝔇 (vanishFn F0 hF0) g j₀ b r := by
  classical
  set α := chartMap 𝔇 j₀ b with hαdef
  set W : Opens X := 𝔇.U j₀ ⊓ offPos (K + Finsupp.single b 1) with hWdef
  set F : ↥W → ℂ := td.cupRep f ∘ openIncl (inf_le_left : W ≤ 𝔇.U j₀) with hFdef
  -- `F` represents the restricted cup-cochain class on `W`
  have hgF : toGerm W F = rawRestrictG (inf_le_left : W ≤ 𝔇.U j₀) (F0 j₀) := by
    rw [hcomp, ← td.toGerm_cupRep f]
    rfl
  -- punctured neighbourhoods of `b` lie in `W`
  have hWnear : ∀ᶠ x in 𝓝[≠] b, x ∈ W := by
    set T : Finset X := (posSupp (K + Finsupp.single b 1)).erase b with hTdef
    have hTcl : IsClosed ((T : Finset X) : Set X) := T.finite_toSet.isClosed
    have hbT : b ∉ ((T : Finset X) : Set X) := by simp [hTdef]
    rw [eventually_nhdsWithin_iff]
    filter_upwards [(𝔇.U j₀).isOpen.mem_nhds hb, hTcl.isOpen_compl.mem_nhds hbT]
      with x hx1 hx2 hxb
    have hxb' : x ≠ b := by simpa using hxb
    refine ⟨hx1, mem_offPos_iff.mpr ?_⟩
    by_contra hpos
    push Not at hpos
    exact hx2 (Finset.mem_erase.mpr ⟨hxb', mem_posSupp_iff.mpr hpos⟩)
  -- the ambient-chart meromorphy and EXACT order `−K b − 1` of the honest representative
  have hcmer : MeromorphicAt (Gext (td.cupRep f) ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) :=
    Gext_meromorphicAt (td.isMeromorphic_cupRep f) hb
  have hcord : meromorphicOrderAt (Gext (td.cupRep f) ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) = ((-(K b) - 1 : ℤ) : WithTop ℤ) := by
    rw [← ordU_eq_orderAt_Gext (td.cupRep f) hb]
    exact td.ordU_cupRep hn hm
  -- transfer to the `W`-restricted extension (they agree on punctured neighbourhoods)
  have hGFeq : ∀ᶠ x in 𝓝[≠] b, Gext F x = Gext (td.cupRep f) x := by
    filter_upwards [hWnear] with x hxW
    rw [Gext_apply_mem F hxW, Gext_apply_mem (td.cupRep f)
      ((inf_le_left : W ≤ 𝔇.U j₀) hxW : x ∈ 𝔇.U j₀)]
    rfl
  have hψtend : Tendsto (chartAt (H := ℂ) b).symm (𝓝[≠] ((chartAt (H := ℂ) b) b)) (𝓝[≠] b) := by
    have h := (chartAt (H := ℂ) b).symm.tendsto_nhdsNE (x := (chartAt (H := ℂ) b) b)
      (by simp [(chartAt (H := ℂ) b).map_source (mem_chart_source ℂ b)])
    simpa [(chartAt (H := ℂ) b).left_inv (mem_chart_source ℂ b)] using h
  have hreadeq : (Gext F ∘ (chartAt (H := ℂ) b).symm)
      =ᶠ[𝓝[≠] ((chartAt (H := ℂ) b) b)] (Gext (td.cupRep f) ∘ (chartAt (H := ℂ) b).symm) :=
    hψtend.eventually hGFeq
  have hFmer : MeromorphicAt (Gext F ∘ (chartAt (H := ℂ) b).symm) ((chartAt (H := ℂ) b) b) :=
    hcmer.congr hreadeq.symm
  have hFord : meromorphicOrderAt (Gext F ∘ (chartAt (H := ℂ) b).symm)
      ((chartAt (H := ℂ) b) b) = ((-(K b) - 1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr hreadeq]
    exact hcord
  -- the read-back: the extraction agrees with the honest representative near `b`
  have hread : ∀ᶠ x in 𝓝[≠] b,
      vanishFn F0 hF0 j₀ x
        = Gext F x :=
    holoFn_eventuallyEq_near_marked (restrict_mem_omegaDGerm_zero hF0 j₀) hgF hWnear hFmer hFord
  -- transfer the agreement to the center chart
  have hbsrc : b ∈ (chartAt ℂ (𝔇.center j₀)).source := mem_chartSource_of_mem_U 𝔇 hb
  have hctend : Tendsto (chartAt ℂ (𝔇.center j₀)).symm (𝓝[≠] α) (𝓝[≠] b) := by
    have hli : (chartAt ℂ (𝔇.center j₀)).symm α = b :=
      (chartAt ℂ (𝔇.center j₀)).left_inv hbsrc
    have h := (chartAt ℂ (𝔇.center j₀)).symm.tendsto_nhdsNE (x := α)
      (by simpa using (chartAt ℂ (𝔇.center j₀)).map_source hbsrc)
    rwa [hli] at h
  have hcenterEq : ∀ᶠ ζ in 𝓝[≠] α,
      vanishFn F0 hF0 j₀
          ((chartAt ℂ (𝔇.center j₀)).symm ζ)
        = Gext (td.cupRep f) ((chartAt ℂ (𝔇.center j₀)).symm ζ) := by
    filter_upwards [hctend.eventually hread, hctend.eventually hGFeq] with ζ h1 h2
    exact h1.trans h2
  -- the center-chart order of the honest representative
  obtain ⟨hcmer', hcord'⟩ := centerRead_data hb (Gext (td.cupRep f)) hcmer
  rw [hcord] at hcord'
  -- the slot order is exactly `K b`
  obtain ⟨u, huan, hu0, hgv⟩ := hexact b j₀ hb
  have hgan : AnalyticAt ℂ (g j₀) α := hg.1 j₀ b hb
  have hgord : meromorphicOrderAt (g j₀) α = ((K b : ℤ) : WithTop ℤ) := by
    refine (meromorphicOrderAt_eq_int_iff hgan.meromorphicAt).mpr ⟨u, huan, hu0, ?_⟩
    filter_upwards [hgv.filter_mono nhdsWithin_le_nhds] with ζ hζ
    rw [hζ, smul_eq_mul]
    congr 1
    rw [show (ζ - α) ^ (K b) = (ζ - α) ^ (((K b).toNat : ℤ)) from by
      rw [Int.toNat_of_nonneg hKb], zpow_natCast]
  -- the product order is exactly `−1`
  have hRgmer : MeromorphicAt (fun ζ =>
      Gext (td.cupRep f) ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ) α := by
    have h := hcmer'.mul hgan.meromorphicAt
    exact h
  have hRgord : meromorphicOrderAt (fun ζ =>
      Gext (td.cupRep f) ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ) α
      = ((-1 : ℤ) : WithTop ℤ) := by
    rw [show (fun ζ => Gext (td.cupRep f) ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
        = (fun ζ => Gext (td.cupRep f) ((chartAt ℂ (𝔇.center j₀)).symm ζ)) * g j₀ from rfl,
      meromorphicOrderAt_mul hcmer' hgan.meromorphicAt, hcord', hgord]
    have harith : (-(K b) - 1) + K b = (-1 : ℤ) := by ring
    exact_mod_cast congrArg (fun z : ℤ => (z : WithTop ℤ)) harith
  -- transfer to the extraction's slot-product
  have htargetEq : (fun ζ =>
      vanishFn F0 hF0 j₀
          ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ)
      =ᶠ[𝓝[≠] α] (fun ζ =>
        Gext (td.cupRep f) ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ) := by
    filter_upwards [hcenterEq] with ζ hζ
    rw [hζ]
  have htmer : MeromorphicAt (fun ζ =>
      vanishFn F0 hF0 j₀
        ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ) α :=
    hRgmer.congr htargetEq.symm
  have htord : meromorphicOrderAt (fun ζ =>
      vanishFn F0 hF0 j₀
        ((chartAt ℂ (𝔇.center j₀)).symm ζ) * g j₀ ζ) α = ((-1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_congr htargetEq]
    exact hRgord
  -- order exactly `−1` ⟹ the simple-pole shape with nonzero residue
  obtain ⟨w', hw'an, hw'0, hw'e⟩ := (meromorphicOrderAt_eq_int_iff htmer).mp htord
  refine ⟨w' α, hw'0, ?_⟩
  obtain ⟨p, hp⟩ := hw'an
  refine ⟨dslope w' α, ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩, ?_⟩
  filter_upwards [hw'e, eventually_mem_nhdsWithin] with ζ hζ hζne
  have hζα : ζ ≠ α := hζne
  rw [hζ, dslope_of_ne _ hζα, slope_def_field, zpow_neg_one, smul_eq_mul, div_eq_mul_inv]
  ring

end TestCocycleData

/-- **THE §17.7 EVALUATION** — the fine-sheaf residue functional does NOT vanish on the cup of
`f ∈ L(K−E)` with the skyscraper test cocycle at a cover-isolated forced bad point of exact
order `n = m − K b`: the cup cocycle is a `B¹(𝒪_{K+b})`-coboundary with ONE marked simple-pole
point, every other `(K+b)`-point extends (the DescentVanish product-germ trick), and the marked
evaluation engine gives `resCocycle (f ⌣ δ⁰n̂) = −r ≠ 0`. -/
theorem resCocycle_cup_testCocycle_ne_zero (hsep : SeparatesPoles 𝔇 K)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    {E : Divisor X} {j₀ : 𝔇.toFiniteCover.ι} {b : X} {hb : b ∈ (𝔇.U j₀ : Set X)} {m : ℤ}
    (td : TestCocycleData 𝔇 E j₀ b hb m) (hbiso : MLIsolated 𝔇 j₀ b) (hKb : 0 ≤ K b)
    (f : ↥(linearSystem (X := X) (K - E)))
    {n : ℤ} (hn : (f : MeromorphicFunction X).orderW b = (n : WithTop ℤ)) (hm : m = n + K b) :
    resCocycle 𝔇 hsep g hg
      (cupCocyclesMap (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f.2 (td.cocycle hbiso)) ≠ 0 := by
  classical
  have hF0 : cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) (f : MeromorphicFunction X)
      td.cochain ∈ 𝔇.toFiniteCover.toFiniteFamily.sections0 (K + Finsupp.single b 1) :=
    td.cup_mem_sections0 f.2 hn hm
  have hsep' : SeparatesPoles 𝔇 (K + Finsupp.single b 1) := separatesPoles_add_single hsep hbiso
  set z : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 K) :=
    cupCocyclesMap (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) f.2 (td.cocycle hbiso) with hzdef
  -- the cup cocycle is the coboundary of the cup 0-cochain
  have hcb : (z : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      = 𝔇.toFiniteCover.toFiniteFamily.cechDelta0
        (cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily) (f : MeromorphicFunction X)
          td.cochain) := by
    have h1 := LinearMap.congr_fun
      (cupCochain1_comp_cechDelta0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily)
        (f : MeromorphicFunction X)) td.cochain
    simp only [LinearMap.comp_apply] at h1
    rw [hzdef, cupCocyclesMap_coe, td.cocycle_coe]
    exact h1
  -- the `Z¹(𝒪_K)` cup cocycle, viewed at the marked level `K + b`
  have hzK' : (z : 𝔇.toFiniteCover.toFiniteFamily.Cochain1)
      ∈ 𝔇.toFiniteCover.toFiniteFamily.cocycles1 (K + Finsupp.single b 1) := by
    obtain ⟨hker, hsec⟩ := Submodule.mem_inf.mp z.2
    refine Submodule.mem_inf.mpr ⟨hker, fun p => ?_⟩
    refine OmegaDGerm_mono (fun x _ => ?_) (hsec p)
    by_cases hxb : x = b
    · subst hxb
      rw [Kb_apply_self]
      omega
    · rw [Kb_apply_ne hxb]
  set z' : ↥(𝔇.toFiniteCover.toFiniteFamily.cocycles1 (K + Finsupp.single b 1)) :=
    ⟨(z : 𝔇.toFiniteCover.toFiniteFamily.Cochain1), hzK'⟩ with hz'def
  obtain ⟨r, hr0, hpole⟩ := td.exists_slotProductSimplePoleAt hn hm hKb hg hexact hF0 rfl
  rw [resCocycle_apply]
  have heval : resFunctional 𝔇 (⟨glueCoeff 𝔇 (cocycleFn 𝔇 hsep z) g,
      glueCoeff_cocycleFn_mem 𝔇 hsep z hg⟩ : oneOneCoeff 𝔇) = -r := by
    refine resFunctional_eq_neg_residue_of_mero_coboundary
      (S := posSupp (K + Finsupp.single b 1)) (w := cocycleFn 𝔇 hsep z)
      (h := vanishFn (cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily)
        (f : MeromorphicFunction X) td.cochain) hF0)
      _ rfl hg ?_ (smoothOnSetsOff_vanishFn hF0) (holomorphicOnSetsOff_vanishFn hF0) ?_ ?_
      hbiso hpole ?_
    · -- every bad point is cover-isolated
      intro a haS
      by_cases hab : a = b
      · exact ⟨j₀, hab ▸ hbiso⟩
      · refine exists_isolated_of_separatesPoles 𝔇 hsep ?_
        have h1 := mem_posSupp_iff.mp haS
        rwa [Kb_apply_ne hab] at h1
    · -- the extraction is honestly the coboundary of the off-(K+b)-points extraction
      have h1 : IsCoboundaryOn 𝔇 (cocycleFn 𝔇 hsep' z')
          (vanishFn (cupCochain0 (𝔘 := 𝔇.toFiniteCover.toFiniteFamily)
            (f : MeromorphicFunction X) td.cochain) hF0) :=
        isCoboundaryOn_cocycleFn_vanishFn hsep' z' hF0 hcb
      have h2 : cocycleFn 𝔇 hsep z = cocycleFn 𝔇 hsep' z' := rfl
      rwa [h2]
    · -- the marked point is a `(K+b)`-point
      exact mem_posSupp_iff.mpr (by rw [Kb_apply_self]; omega)
    · -- every other `(K+b)`-point extends (product-germ trick at level `K+b`)
      intro a haS hab i₀ hiso'
      have haK' : 0 < (K + Finsupp.single b 1 : Divisor X) a := mem_posSupp_iff.mp haS
      have haK : 0 < K a := by rwa [Kb_apply_ne hab] at haK'
      obtain ⟨u, huan, hu0, hgv⟩ := hexact a i₀ hiso'.1
      have hgv' : ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i₀ a), g i₀ ζ
          = (ζ - chartMap 𝔇 i₀ a) ^ ((K + Finsupp.single b 1 : Divisor X) a).toNat * u ζ := by
        rw [show ((K + Finsupp.single b 1 : Divisor X) a).toNat = (K a).toNat from by
          rw [Kb_apply_ne hab]]
        exact hgv
      exact slotProductExtendsAt_vanishFn hF0 hg haK' hiso' huan hgv'
  rw [heval]
  exact neg_ne_zero.mpr hr0

/-! ## Part 5 — the conditional headline: `UnwindRegularity` for the concrete fine-sheaf residue

The remaining hypothesis is the **cover-isolation discipline** `BadPointsIsolated`: every class
outside the image must admit SOME cover-isolated bad point.  This is the genuine residual wall
(`docs/planning/UNWIND_BLOCKER.md`): forced bad points live in `supp(D−E)`, which is arbitrary
as `E` ranges below `D`, so no fixed cover satisfies the discipline unconditionally — removing
it needs the multi-chart (non-isolated) evaluation engine. -/

/-- **The cover-isolation discipline** for the level-`D` unwinding: every level-`E` class
outside the `L(K−D)` bounds has a cover-isolated bad point of finite order in the jump window
`[E b − K b, D b − K b)`.  (`exists_bad_point` always supplies the window; the ISOLATION is the
extra demand.) -/
def BadPointsIsolated (𝔇 : ChartDiskCover X) (K D : Divisor X) : Prop :=
  ∀ (E : Divisor X), (∀ x, E x ≤ D x) →
    ∀ f : ↥(linearSystem (X := X) (K - E)),
      (f : MeromorphicFunction X) ∉ linearSystem (X := X) (K - D) →
      ∃ (b : X) (j₀ : 𝔇.toFiniteCover.ι) (n : ℤ),
        MLIsolated 𝔇 j₀ b ∧ (f : MeromorphicFunction X).orderW b = (n : WithTop ℤ) ∧
        E b - K b ≤ n ∧ n < D b - K b

/-- **THE CONDITIONAL §17.7 HEADLINE — `UnwindRegularity` is a THEOREM for the concrete
fine-sheaf residue at every level `D` whose bad points are cover-isolated.**  The hypotheses
are exactly the R-lane interface for the concrete `G`: pole separation, the analytic `dz`-slot
with exact divisor `K ≥ 0`, the corrected §17.6 witness, the exact-order local Mittag–Leffler
witness (PROVEN for the canonical chart-disk cover), plus the isolation discipline.  Forster
(GTM 81), Lemma 17.7. -/
theorem unwindRegularity_concrete_of_isolated
    (hsep : SeparatesPoles 𝔇 K) {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    (hg : IsOneZeroCoeff 𝔇 g) (hexact : SlotExactK 𝔇 g K)
    (hwit : CupMLWitnessR 𝔇 hsep g) (hwitness : ExactOrderWitness 𝔇)
    (hKeff : ∀ x, 0 ≤ K x) (D : Divisor X) (hiso : BadPointsIsolated 𝔇 K D) :
    ((cousinResidueData_of_witnessR hsep g hg (SlotMatchesK_of_exact hexact)
      hwit).toGlobalResidue).UnwindRegularity D := by
  classical
  refine GlobalResidue.unwindRegularity_of_detects _ D ?_
  intro E hED v hno
  obtain ⟨fE, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  -- the forced cover-isolated bad point with its order window
  rw [exists_lSysInclMono_eq_iff hED fE] at hno
  obtain ⟨b, j₀, n, hbiso, hn, hge, hlt⟩ := hiso E hED fE hno
  have hb : b ∈ (𝔇.U j₀ : Set X) := hbiso.1
  -- the admissible level `m = n + K b`: `E b ≤ m` and `m + 1 ≤ D b`
  set m : ℤ := n + K b with hmdef
  have hmE : E b ≤ m := by
    have := hKeff b
    omega
  have hmD : m + 1 ≤ D b := by omega
  obtain ⟨td⟩ := TestCocycleData.exists_of_witness hwitness hb hmE
  refine ⟨Submodule.Quotient.mk (td.cocycle hbiso),
    td.h1InclMono_cocycle_eq_zero hbiso hED hmD, ?_⟩
  -- the pairing factors through the cup and evaluates to the nonzero marked residue
  rw [GlobalResidue.pairing_apply, cup_mk, cupH1_mk]
  exact resCocycle_cup_testCocycle_ne_zero hsep hg hexact td hbiso (hKeff b) fE hn hmdef

end Evaluation

end Dolbeault

end Jacobians

end
