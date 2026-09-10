/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailSpaceGlobal
import KirovDolbeault.Dolbeault.SerreOmega0
import KirovDolbeault.Dolbeault.SerreUnwindDetect
import KirovDolbeault.Dolbeault.ChartDiskCoverGeneric

/-!
# Tail `H¹`, finiteness, and tail Riemann–Roch I (tail tower T4)

Miranda Ch. VI over the T2–T3 substrate (route: `docs/planning/TAILRR_ROUTE.md`):

* `H1Tail D := GlobalTails X ⧸ (im α_D ⊔ 𝒰[D])` — the Laurent-tail first cohomology
  (ambient-quotient model: quotienting by the upper space implements the restriction to
  `𝒯[D]` without subtype quotients); `h1TailDim`.
* `h1TailMapMono` — the canonical map `H¹(D) → H¹(D')` (`D ≤ D'`; the denominators are
  MONOTONE, `tailCoker_mono`), SURJECTIVE.
* The window bookkeeping, all proven as submodule identities (pure coefficient algebra) in
  the Pi-model `WindowModel` coordinates: `windowReadQ : L(D')/junk → 𝒲(D,D')` with kernel
  the image of `L(D)/junk` (`ker_windowReadQ`), and `windowToH1 : 𝒲(D,D') → H¹(D)` with
  kernel `range windowReadQ` (`ker_windowToH1`) and range `ker h1TailMapMono`
  (`range_windowToH1`).
* **Finiteness** (`finiteDimensional_H1Tail`): every tail class dies under deep truncation
  (`exists_truncTails_eq_zero`), so an independent family lives in ONE window image, whose
  dimension is uniformly bounded via the Riemann inequality (`riemannRoch_inequality` — the
  M-bound, the only Čech input).  No Čech vanishing, no cup-kill, no duality.
* **Tail Riemann–Roch I** (`tail_riemannRoch_I`):
  `l(D) − h¹_t(D) = deg D + 1 − tailGenus X`, `tailGenus X := h¹_t(0)`, for EVERY
  divisor — χ-constancy on comparable pairs (`tailChi_pair`) + the positive-part common
  refinement.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI §3.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Filter Module

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians

namespace Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 0 — tail `H¹` and the connecting maps -/

/-- The denominator of the tail `H¹`: the tail-map image together with the upper space. -/
def tailCoker (D : Divisor X) : Submodule ℂ (GlobalTails X) :=
  LinearMap.range (tailMap D) ⊔ upperSpace D

/-- **The Laurent-tail first cohomology** `H¹(D) = 𝒯[D] ⧸ im α_D` (Miranda VI.3), realized
as the ambient quotient `GlobalTails X ⧸ (im α_D ⊔ 𝒰[D])`. -/
abbrev H1Tail (D : Divisor X) : Type _ := GlobalTails X ⧸ tailCoker (X := X) D

/-- `h¹_t(D) = dim H¹(D)`. -/
def h1TailDim (D : Divisor X) : ℕ := Module.finrank ℂ (H1Tail (X := X) D)

variable {D D' : Divisor X}

/-- A tail in `𝒰[D]` is `0` in `H¹(D)`. -/
theorem mk_eq_zero_of_mem_upperSpace {t : GlobalTails X} (ht : t ∈ upperSpace D) :
    (Submodule.Quotient.mk t : H1Tail (X := X) D) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_sup_right ht

/-- The tail-map image dies in `H¹(D)`. -/
theorem mk_tailMap_eq_zero (f : MeromorphicFunction X) :
    (Submodule.Quotient.mk (tailMap D f) : H1Tail (X := X) D) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_sup_left ⟨f, rfl⟩

/-- **Monotonicity of the denominators** (`D ≤ D'`): the level-`D` tail of any `f` differs
from its level-`D'` tail by an upper-space term. -/
theorem tailCoker_mono (hDD' : ∀ x, D x ≤ D' x) :
    tailCoker (X := X) D ≤ tailCoker D' := by
  refine sup_le ?_ (le_trans (upperSpace_mono hDD') le_sup_right)
  rintro - ⟨f, rfl⟩
  have hsplit : tailMap D f
      = tailMap D' f + (tailMap D f - truncTails D' (tailMap D f)) := by
    rw [truncTails_tailMap hDD' f]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨f, rfl⟩)
    (Submodule.mem_sup_right (sub_truncTails_mem_upperSpace D' _))

/-- **The connecting map** `H¹(D) → H¹(D')` (`D ≤ D'`): the quotient factor map. -/
def h1TailMapMono (hDD' : ∀ x, D x ≤ D' x) :
    H1Tail (X := X) D →ₗ[ℂ] H1Tail (X := X) D' :=
  Submodule.mapQ _ _ LinearMap.id (fun t ht => by
    rw [Submodule.mem_comap, LinearMap.id_apply]
    exact tailCoker_mono hDD' ht)

@[simp] theorem h1TailMapMono_mk (hDD' : ∀ x, D x ≤ D' x) (t : GlobalTails X) :
    h1TailMapMono hDD' (Submodule.Quotient.mk t) = Submodule.Quotient.mk t := rfl

/-- The connecting map is **surjective**. -/
theorem h1TailMapMono_surjective (hDD' : ∀ x, D x ≤ D' x) :
    Function.Surjective (h1TailMapMono (X := X) hDD') := by
  intro ξ
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  exact ⟨Submodule.Quotient.mk t, rfl⟩

/-! ## Part 1 — the window bookkeeping maps (in the Pi-model coordinates) -/

/-- The window space sits inside `𝒯[D]`. -/
theorem windowSpace_le_tailSpace (D D' : Divisor X) :
    windowSpace (X := X) D D' ≤ tailSpace (X := X) D :=
  Finsupp.supported_mono fun _ hq => hq.1

/-- The window space sits inside `𝒰[D']`. -/
theorem windowSpace_le_upperSpace (D D' : Divisor X) :
    windowSpace (X := X) D D' ≤ upperSpace (X := X) D' :=
  Finsupp.supported_mono fun _ hq => hq.2

/-- A window element vanishes at slots below the `−D'` cut. -/
theorem windowSpace_apply_eq_zero_of_below {w : GlobalTails X}
    (hw : w ∈ windowSpace (X := X) D D') {q : X × ℤ} (hq : q.2 < -(D' q.1)) :
    w q = 0 := by
  by_contra hne
  have hsupp : q ∈ w.support := Finsupp.mem_support_iff.mpr hne
  have := hw hsupp
  simp only [windowSet, belowSet, Set.mem_diff, Set.mem_setOf_eq, not_lt] at this
  omega

/-- The tail of an `L(D')` function lies in the window `𝒲(D, D')` (`D ≤ D'`). -/
theorem tailMap_mem_windowSpace (hDD' : ∀ x, D x ≤ D' x) {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) D') :
    tailMap D f ∈ windowSpace (X := X) D D' := by
  have h0 : truncTails D' (tailMap D f) = 0 := by
    rw [truncTails_tailMap hDD' f]
    exact (tailMap_eq_zero_iff D' f).mpr hf
  have := sub_truncTails_mem_windowSpace (D' := D') (tailMap_mem_tailSpace D f)
  rwa [h0, sub_zero] at this

/-- **The window read of `L(D')`**: `f ↦ α_D f`, landing in the window (`D ≤ D'`). -/
def windowRead (hDD' : ∀ x, D x ≤ D' x) :
    ↥(linearSystem (X := X) D') →ₗ[ℂ] ↥(windowSpace (X := X) D D') :=
  LinearMap.codRestrict (windowSpace (X := X) D D')
    ((tailMap D).comp (linearSystem (X := X) D').subtype)
    (fun f => tailMap_mem_windowSpace hDD' f.2)

@[simp] theorem windowRead_coe (hDD' : ∀ x, D x ≤ D' x)
    (f : ↥(linearSystem (X := X) D')) :
    (windowRead hDD' f : GlobalTails X) = tailMap D (f : MeromorphicFunction X) := rfl

/-- The window read in the Pi-model coordinates. -/
def windowReadM (hDD' : ∀ x, D x ≤ D' x) :
    ↥(linearSystem (X := X) D') →ₗ[ℂ] WindowModel (X := X) D D' :=
  (windowModelEquiv D D').toLinearMap.comp (windowRead hDD')

theorem windowReadM_apply (hDD' : ∀ x, D x ≤ D' x) (f : ↥(linearSystem (X := X) D')) :
    windowReadM hDD' f = windowModelEquiv D D' (windowRead hDD' f) := rfl

theorem windowReadM_eq_zero_iff (hDD' : ∀ x, D x ≤ D' x)
    (f : ↥(linearSystem (X := X) D')) :
    windowReadM hDD' f = 0 ↔ tailMap D (f : MeromorphicFunction X) = 0 := by
  rw [windowReadM_apply, LinearEquiv.map_eq_zero_iff, Subtype.ext_iff, windowRead_coe,
    ZeroMemClass.coe_zero]

/-- The junk-free descent of the window read: `L(D')/junk → 𝒲(D,D')`. -/
def windowReadQ (hDD' : ∀ x, D x ≤ D' x) :
    lSysModule (X := X) D' →ₗ[ℂ] WindowModel (X := X) D D' := by
  refine Submodule.liftQ _ (windowReadM hDD') ?_
  intro f hf
  rw [Submodule.submoduleOf, Submodule.mem_comap] at hf
  rw [LinearMap.mem_ker, windowReadM_eq_zero_iff]
  have hjunk : (f : MeromorphicFunction X) - 0 ∈ germZeroSubmodule (X := X) := by
    rwa [sub_zero]
  rw [tailMap_eq_of_sub_germZero hjunk D, map_zero]

@[simp] theorem windowReadQ_mk (hDD' : ∀ x, D x ≤ D' x)
    (f : ↥(linearSystem (X := X) D')) :
    windowReadQ hDD' (Submodule.Quotient.mk f) = windowReadM hDD' f := rfl

/-- The monotone junk-free inclusion is injective. -/
theorem lSysInclMono_injective (hDD' : ∀ x, D x ≤ D' x) :
    Function.Injective (lSysInclMono (X := X) hDD') := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr ?_
  intro u hu
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [LinearMap.mem_ker, lSysInclMono_mk, Submodule.Quotient.mk_eq_zero] at hu
  rw [Submodule.Quotient.mk_eq_zero]
  exact hu

/-- **Kernel of the window read = the image of `L(D)/junk`** (Miranda exactness at `L(D')`). -/
theorem ker_windowReadQ (hDD' : ∀ x, D x ≤ D' x) :
    LinearMap.ker (windowReadQ (X := X) hDD') = LinearMap.range (lSysInclMono hDD') := by
  ext ξ
  constructor
  · intro hξ
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [LinearMap.mem_ker, windowReadQ_mk, windowReadM_eq_zero_iff] at hξ
    have hfD : (f : MeromorphicFunction X) ∈ linearSystem (X := X) D :=
      (tailMap_eq_zero_iff D _).mp hξ
    refine ⟨Submodule.Quotient.mk ⟨(f : MeromorphicFunction X), hfD⟩, ?_⟩
    rw [lSysInclMono_mk]
    rfl
  · rintro ⟨u, rfl⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [LinearMap.mem_ker, lSysInclMono_mk, windowReadQ_mk, windowReadM_eq_zero_iff]
    exact (tailMap_eq_zero_iff D _).mpr g.2

/-- The window-to-`H¹` map `𝒲(D,D') → H¹(D)`, from the Pi-model coordinates. -/
def windowToH1 (D D' : Divisor X) :
    WindowModel (X := X) D D' →ₗ[ℂ] H1Tail (X := X) D :=
  ((tailCoker (X := X) D).mkQ.comp (windowSpace (X := X) D D').subtype).comp
    (windowModelEquiv D D').symm.toLinearMap

theorem windowToH1_apply (m : WindowModel (X := X) D D') :
    windowToH1 D D' m
      = Submodule.Quotient.mk (((windowModelEquiv D D').symm m : GlobalTails X)) := rfl

/-- The window read dies in `H¹(D)` (the easy composite vanishing, isolated to keep the
elaboration cheap). -/
theorem windowToH1_windowReadM (hDD' : ∀ x, D x ≤ D' x)
    (f : ↥(linearSystem (X := X) D')) :
    windowToH1 (X := X) D D' (windowReadM hDD' f) = 0 := by
  rw [windowReadM_apply, windowToH1_apply, LinearEquiv.symm_apply_apply, windowRead_coe]
  exact mk_tailMap_eq_zero (f : MeromorphicFunction X)

/-- **Kernel of the window-to-`H¹` map = the window read image** (exactness at the window). -/
theorem ker_windowToH1 (hDD' : ∀ x, D x ≤ D' x) :
    LinearMap.ker (windowToH1 (X := X) D D') = LinearMap.range (windowReadQ hDD') := by
  ext m
  constructor
  · intro hm
    set w : ↥(windowSpace (X := X) D D') := (windowModelEquiv D D').symm m with hwdef
    rw [LinearMap.mem_ker, windowToH1_apply, ← hwdef, Submodule.Quotient.mk_eq_zero] at hm
    obtain ⟨a, ha, u, hu, hau⟩ := Submodule.mem_sup.mp hm
    obtain ⟨f₀, rfl⟩ := ha
    -- the upper part is squeezed to `0` between `𝒯[D]` and `𝒰[D]`
    have hu_tail : u ∈ tailSpace (X := X) D := by
      have hueq : u = (w : GlobalTails X) - tailMap D f₀ := by
        rw [← hau]
        abel
      rw [hueq]
      exact Submodule.sub_mem _ (windowSpace_le_tailSpace D D' w.2)
        (tailMap_mem_tailSpace D f₀)
    have hu0 : u = 0 :=
      Submodule.disjoint_def.mp (tailSpace_inf_upperSpace D) u hu_tail hu
    have hweq : (w : GlobalTails X) = tailMap D f₀ := by
      rw [← hau, hu0, add_zero]
    -- the window support forces the `L(D')` bound on `f₀`
    have hf₀D' : f₀ ∈ linearSystem (X := X) D' := by
      intro p
      refine (MeromorphicFunction.orderW_ge_iff_coeffAt_vanish f₀ p (-(D' p))).mpr ?_
      intro k hk
      have hDp : k < -(D p) := by
        have := hDD' p
        omega
      have hread : (w : GlobalTails X) (p, k) = tailMap D f₀ (p, k) := by rw [hweq]
      rw [tailMap_apply_coeff, if_pos hDp] at hread
      rw [← hread]
      exact windowSpace_apply_eq_zero_of_below w.2 (q := (p, k)) hk
    refine ⟨Submodule.Quotient.mk ⟨f₀, hf₀D'⟩, ?_⟩
    rw [windowReadQ_mk, windowReadM_apply]
    have hwr : windowRead hDD' ⟨f₀, hf₀D'⟩ = w :=
      Subtype.ext (by rw [windowRead_coe]; exact hweq.symm)
    rw [hwr, hwdef, LinearEquiv.apply_symm_apply]
  · rintro ⟨u, rfl⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [LinearMap.mem_ker, windowReadQ_mk]
    exact windowToH1_windowReadM hDD' f

/-- **Range of the window-to-`H¹` map = kernel of the connecting map** (exactness at
`H¹(D)`). -/
theorem range_windowToH1 (hDD' : ∀ x, D x ≤ D' x) :
    LinearMap.range (windowToH1 (X := X) D D')
      = LinearMap.ker (h1TailMapMono hDD') := by
  ext ξ
  constructor
  · rintro ⟨m, rfl⟩
    rw [LinearMap.mem_ker, windowToH1_apply, h1TailMapMono_mk,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right
      (windowSpace_le_upperSpace D D' ((windowModelEquiv D D').symm m).2)
  · intro hξ
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [LinearMap.mem_ker, h1TailMapMono_mk, Submodule.Quotient.mk_eq_zero] at hξ
    obtain ⟨a, ha, u', hu', hau⟩ := Submodule.mem_sup.mp hξ
    obtain ⟨f, rfl⟩ := ha
    -- the window representative of the class
    set w₀ : GlobalTails X := truncTails D (t : GlobalTails X) - tailMap D f with hw₀def
    have hw₀tail : w₀ ∈ tailSpace (X := X) D :=
      Submodule.sub_mem _ (truncTails_mem D t) (tailMap_mem_tailSpace D f)
    have hw₀trunc : truncTails D' w₀ = 0 := by
      rw [hw₀def, map_sub, truncTails_comp hDD', truncTails_tailMap hDD' f, ← hau,
        map_add, truncTails_eq_zero_of_mem_upperSpace hu',
        truncTails_eq_self_of_mem (tailMap_mem_tailSpace D' f), add_zero]
      exact sub_self _
    have hw₀win : w₀ ∈ windowSpace (X := X) D D' := by
      have := sub_truncTails_mem_windowSpace (D' := D') hw₀tail
      rwa [hw₀trunc, sub_zero] at this
    refine ⟨windowModelEquiv D D' ⟨w₀, hw₀win⟩, ?_⟩
    rw [windowToH1_apply, LinearEquiv.symm_apply_apply, Submodule.Quotient.eq]
    have hsplit : w₀ - t = -(tailMap D f) - (t - truncTails D t) := by
      rw [hw₀def]
      abel
    show w₀ - t ∈ tailCoker (X := X) D
    rw [hsplit]
    exact Submodule.sub_mem _
      (Submodule.neg_mem _ (Submodule.mem_sup_left ⟨f, rfl⟩))
      (Submodule.mem_sup_right (sub_truncTails_mem_upperSpace D _))

/-! ## Part 2 — deep truncation kills any finite family of tails -/

/-- **Deep-truncation kill**: any finite family of tails is annihilated by the truncation to
a deep enough level `D' ≥ D`. -/
theorem exists_truncTails_eq_zero (T : Finset (GlobalTails X)) (D : Divisor X) :
    ∃ D' : Divisor X, (∀ x, D x ≤ D' x) ∧ ∀ t ∈ T, truncTails D' t = 0 := by
  classical
  set S : Finset (X × ℤ) := T.biUnion Finsupp.support with hSdef
  set B : Divisor X := ∑ q ∈ S, Finsupp.single q.1 (max 0 (-q.2 - D q.1)) with hBdef
  have hBnonneg : ∀ x, 0 ≤ B x := by
    intro x
    rw [hBdef, Finset.sum_apply']
    refine Finset.sum_nonneg fun q _ => ?_
    rw [Finsupp.single_apply]
    split <;> omega
  have hBbig : ∀ q ∈ S, -q.2 - D q.1 ≤ B q.1 := by
    intro q hq
    rw [hBdef, Finset.sum_apply']
    calc -q.2 - D q.1 ≤ max 0 (-q.2 - D q.1) := le_max_right _ _
      _ = (fun q' : X × ℤ => (Finsupp.single q'.1 (max 0 (-q'.2 - D q'.1))) q.1) q := by
          simp only [Finsupp.single_eq_same]
      _ ≤ ∑ q' ∈ S, (Finsupp.single q'.1 (max 0 (-q'.2 - D q'.1))) q.1 := by
          refine Finset.single_le_sum (f := fun q' : X × ℤ =>
            (Finsupp.single q'.1 (max 0 (-q'.2 - D q'.1))) q.1) (fun q' _ => ?_) hq
          simp only [Finsupp.single_apply]
          split <;> omega
  refine ⟨D + B, fun x => by
    rw [Finsupp.add_apply]
    have := hBnonneg x
    omega, ?_⟩
  intro t ht
  ext q
  rw [truncTails_apply, Finsupp.coe_zero, Pi.zero_apply]
  split
  · rename_i hcut
    by_contra hne
    have hqS : q ∈ S := Finset.mem_biUnion.mpr ⟨t, ht, Finsupp.mem_support_iff.mpr hne⟩
    have := hBbig q hqS
    rw [Finsupp.add_apply] at hcut
    omega
  · rfl

/-! ## Part 3 — finiteness of `h¹_t` -/

/-- The canonical M-bound: the Riemann inequality at the chart-disk cover. -/
private theorem riemann_M_bound (D₀ : Divisor X) :
    Divisor.deg X D₀ + 1 - ((chartDiskCover (X := X)).toFiniteCover.h1Dim 0 : ℤ)
      ≤ (lDim (X := X) D₀ : ℤ) :=
  riemannRoch_inequality (chartDiskCover (X := X)).locallyRealizable D₀

/-- The window image dimension, exactly (`D ≤ D'`):
`dim im(𝒲 → H¹(D)) = (deg D' − deg D) − (l(D') − l(D))`. -/
theorem finrank_range_windowToH1 (hDD' : ∀ x, D x ≤ D' x) :
    (finrank ℂ ↥(LinearMap.range (windowToH1 (X := X) D D')) : ℤ)
      = (Divisor.deg X D' - Divisor.deg X D)
        - ((lDim (X := X) D' : ℤ) - lDim (X := X) D) := by
  classical
  haveI hFDw : FiniteDimensional ℂ ↥(windowSpace (X := X) D D') :=
    finiteDimensional_windowSpace D D'
  haveI hFDm : FiniteDimensional ℂ (WindowModel (X := X) D D') := inferInstance
  haveI hFD' : FiniteDimensional ℂ (lSysModule (X := X) D') :=
    ((chartDiskCover (X := X)).toFiniteCover.globalSectionsEquivQuot
      (D := D')).symm.finiteDimensional
  haveI hFD : FiniteDimensional ℂ (lSysModule (X := X) D) :=
    ((chartDiskCover (X := X)).toFiniteCover.globalSectionsEquivQuot
      (D := D)).symm.finiteDimensional
  -- rank–nullity for the two window maps
  have hrn1 := LinearMap.finrank_range_add_finrank_ker (windowToH1 (X := X) D D')
  have hrn2 := LinearMap.finrank_range_add_finrank_ker (windowReadQ (X := X) hDD')
  -- identify the kernels
  have hker1 : finrank ℂ ↥(LinearMap.ker (windowToH1 (X := X) D D'))
      = finrank ℂ ↥(LinearMap.range (windowReadQ (X := X) hDD')) := by
    rw [ker_windowToH1 hDD']
  have hker2 : finrank ℂ ↥(LinearMap.ker (windowReadQ (X := X) hDD'))
      = lDim (X := X) D := by
    rw [ker_windowReadQ hDD',
      LinearMap.finrank_range_of_inj (lSysInclMono_injective hDD')]
    rfl
  -- the source dimensions
  have hsrc1 : finrank ℂ (WindowModel (X := X) D D')
      = (Divisor.deg X D' - Divisor.deg X D).toNat := finrank_windowModel hDD'
  have hsrc2 : finrank ℂ (lSysModule (X := X) D') = lDim (X := X) D' := rfl
  -- nonnegativity of the degree difference
  have hdegmono : Divisor.deg X D ≤ Divisor.deg X D' := by
    have heff : ∀ x, (0 : Divisor X) x ≤ (D' - D) x := by
      intro x
      rw [Finsupp.sub_apply]
      have := hDD' x
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    have hnn : 0 ≤ Divisor.deg X (D' - D) := by
      rw [show Divisor.deg X (D' - D) = Finsupp.degree (D' - D) from rfl,
        Finsupp.degree_apply]
      refine Finset.sum_nonneg fun p _ => ?_
      have := heff p
      simpa using this
    rw [Divisor.deg_sub] at hnn
    omega
  rw [hsrc1, hker1] at hrn1
  rw [hsrc2, hker2] at hrn2
  omega

/-- **Finiteness of the tail `H¹`** (Miranda VI.3.4, via the deep-truncation kill and the
Riemann inequality — no duality, no Čech vanishing). -/
theorem finiteDimensional_H1Tail (D : Divisor X) :
    FiniteDimensional ℂ (H1Tail (X := X) D) := by
  classical
  set M : ℕ := (chartDiskCover (X := X)).toFiniteCover.h1Dim 0 with hMdef
  set B : ℤ := (M : ℤ) + (lDim (X := X) D : ℤ) - 1 - Divisor.deg X D with hBdef
  have hcard : ∀ s : Finset (H1Tail (X := X) D),
      (LinearIndependent ℂ fun i : s => (i : H1Tail (X := X) D)) → s.card ≤ B.toNat := by
    intro s hs
    -- representatives and a common kill level
    have hrep : ∀ ξ : H1Tail (X := X) D, ∃ t : GlobalTails X,
        Submodule.Quotient.mk t = ξ := Submodule.Quotient.mk_surjective _
    choose rep hrep using hrep
    obtain ⟨D', hDD', hkill⟩ := exists_truncTails_eq_zero (s.image rep) D
    -- every element of `s` dies at `D'`, hence lives in the window image
    have hmem : ∀ ξ ∈ s, ξ ∈ LinearMap.range (windowToH1 (X := X) D D') := by
      intro ξ hξ
      rw [range_windowToH1 hDD', LinearMap.mem_ker, ← hrep ξ, h1TailMapMono_mk,
        Submodule.Quotient.mk_eq_zero]
      refine Submodule.mem_sup_right ?_
      have hk := hkill (rep ξ) (Finset.mem_image_of_mem rep hξ)
      have := sub_truncTails_mem_upperSpace D' (rep ξ)
      rwa [hk, sub_zero] at this
    haveI : FiniteDimensional ℂ ↥(windowSpace (X := X) D D') :=
      finiteDimensional_windowSpace D D'
    haveI : FiniteDimensional ℂ (WindowModel (X := X) D D') := inferInstance
    haveI : FiniteDimensional ℂ ↥(LinearMap.range (windowToH1 (X := X) D D')) :=
      inferInstance
    -- the independent family lives in the (finite-dimensional) window image
    set v' : s → ↥(LinearMap.range (windowToH1 (X := X) D D')) :=
      fun i => ⟨(i : H1Tail (X := X) D), hmem i i.2⟩ with hv'def
    have hv' : LinearIndependent ℂ v' := by
      refine LinearIndependent.of_comp
        (LinearMap.range (windowToH1 (X := X) D D')).subtype ?_
      exact hs
    have hcardle := hv'.fintype_card_le_finrank
    rw [Fintype.card_coe] at hcardle
    -- the uniform dimension bound
    have hdim := finrank_range_windowToH1 (X := X) hDD'
    have hRie := riemann_M_bound (X := X) D'
    omega
  have hrank : Module.rank ℂ (H1Tail (X := X) D) ≤ B.toNat := rank_le hcard
  exact Module.rank_lt_aleph0_iff.mp
    (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)

/-! ## Part 4 — tail Riemann–Roch I -/

/-- **χ-constancy on comparable pairs**: for `D ≤ D'`,
`l(D) − h¹_t(D) − deg D = l(D') − h¹_t(D') − deg D'`. -/
theorem tailChi_pair (hDD' : ∀ x, D x ≤ D' x) :
    (lDim (X := X) D : ℤ) - h1TailDim (X := X) D - Divisor.deg X D
      = (lDim (X := X) D' : ℤ) - h1TailDim (X := X) D' - Divisor.deg X D' := by
  classical
  haveI := finiteDimensional_H1Tail (X := X) D
  haveI := finiteDimensional_H1Tail (X := X) D'
  -- rank–nullity for the (surjective) connecting map
  have hrn := LinearMap.finrank_range_add_finrank_ker (h1TailMapMono (X := X) hDD')
  have hrange : finrank ℂ ↥(LinearMap.range (h1TailMapMono (X := X) hDD'))
      = h1TailDim (X := X) D' := by
    rw [LinearMap.range_eq_top.mpr (h1TailMapMono_surjective hDD'), finrank_top]
    rfl
  have hker : finrank ℂ ↥(LinearMap.ker (h1TailMapMono (X := X) hDD'))
      = finrank ℂ ↥(LinearMap.range (windowToH1 (X := X) D D')) := by
    rw [range_windowToH1 hDD']
  have hdim := finrank_range_windowToH1 (X := X) hDD'
  have hH1D : finrank ℂ (H1Tail (X := X) D) = h1TailDim (X := X) D := rfl
  omega

/-- The positive part of a divisor: the common refinement of `D` and `0`. -/
def posPart (D : Divisor X) : Divisor X :=
  D.mapRange (fun n => max n 0) (by simp)

theorem le_posPart (D : Divisor X) : ∀ x, D x ≤ posPart D x := fun x => by
  rw [posPart, Finsupp.mapRange_apply]
  exact le_max_left _ _

theorem zero_le_posPart (D : Divisor X) : ∀ x, (0 : Divisor X) x ≤ posPart D x := fun x => by
  rw [posPart, Finsupp.mapRange_apply]
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  exact le_max_right _ _

/-- **The tail (arithmetic) genus** `g_t := h¹_t(0)`. -/
def tailGenus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  h1TailDim (X := X) (0 : Divisor X)

/-- **Tail Riemann–Roch I** (Miranda VI.3.11, the genus-`g_t` form): for EVERY divisor,
`l(D) − h¹_t(D) = deg D + 1 − g_t`. -/
theorem tail_riemannRoch_I (D : Divisor X) :
    (lDim (X := X) D : ℤ) - h1TailDim (X := X) D
      = Divisor.deg X D + 1 - tailGenus X := by
  have h1 := tailChi_pair (X := X) (D := D) (D' := posPart D) (le_posPart D)
  have h2 := tailChi_pair (X := X) (D := 0) (D' := posPart D) (zero_le_posPart D)
  have hl0 : lDim (X := X) (0 : Divisor X) = 1 := lDim_zero_eq_one
  have hd0 : Divisor.deg X (0 : Divisor X) = 0 := Divisor.deg_zero X
  rw [hl0, hd0] at h2
  rw [show tailGenus X = h1TailDim (X := X) (0 : Divisor X) from rfl]
  omega

end Dolbeault

end Jacobians

end
