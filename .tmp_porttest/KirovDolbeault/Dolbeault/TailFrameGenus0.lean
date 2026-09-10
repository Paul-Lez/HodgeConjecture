/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.TailSurjectivity
import KirovDolbeault.Dolbeault.TailFrameWitness

/-!
# The genus-0 arithmetic atom from the meromorphic-frame residue atom (G0 lane)

The G0 atom `hga : 𝔘.h1Dim 0 = 0` at `kirovGenus X = 0` (`docs/planning/G0_BLOCKER.md`)
through the tail tower, reduced to ONE named analytic input.

## The reduction

With both tail towers landed, the pipeline `TailPairFrame X → PairingSurjective →
TailRiemannRoch X → hga` is **genus-free** (`TailPairFrame.pairingSurjective` and
`TailPairFrame.tailRiemannRoch` take no genus hypothesis).  The only genus-dependent link is
frame EXISTENCE: `nonempty_tailPairFrame_of_kirovGenus_pos` (`TailFrameWitness.lean`) builds
the frame from a nonzero HOLOMORPHIC 1-form, which exists only at `kirovGenus X > 0`.

But the frame form's type is already meromorphic: `TailPairFrame.data` is a
`CanonicalForm17Data X` whose `ω₀` is a `MeromorphicOneForm X` — and
`nonempty_canonicalForm17Data` (`CanonicalFormDifferential.lean`) constructs such a datum
UNCONDITIONALLY (`ω₀ = df` of a nonconstant meromorphic `f`, which exists at every genus).
Its slot family is free as well: `slot p := formCoeff ω₀.toFun p` is meromorphic of exact
order `K p` by the datum's own `order_eq`.  So the ONLY missing frame field at genus 0 is the
pair-frame residue theorem `∑ₚ Res_p(F·ω₀) = 0` for a MEROMORPHIC `ω₀` — isolated here as

* `CanonicalForm17Data.ResidueAtom` — the named atom (the exact `resSum` field shape).

It cannot be factored through the proven Gate-A engine
(`SerreResidueTheorem.residueTheorem_unconditional`): a factorization `F·ω₀ = α·g` with `α`
holomorphic would force `div ω₀ ≥ div h` for some global `h` with `ω₀/h` holomorphic, which
is impossible at genus 0 (`deg div ω₀ = −2 < 0`, no nonzero holomorphic forms exist).  The
engine's whole §5 slit tower is parameterized by `coeffAt (α : HolomorphicOneForms X)`
throughout, so the honest discharge is the engine's meromorphic-frame generalization (or the
trace-to-`ℙ¹` of the plain value trace for `ω₀ = df`) — tracked in
`docs/planning/G0_BLOCKER.md`.

## Main declarations

* `CanonicalForm17Data.ResidueAtom` — the single named analytic input: `∑Res(F·ω₀) = 0` over
  `supp(div F) ∪ supp K`, in planar Laurent coefficients, for every meromorphic `F`.
* `TailPairFrame.ofResidueAtom` — the frame from ANY canonical datum + its atom (genus-free).
* `residueAtom_of_form` / `exists_residueAtom_of_kirovGenus_pos` — satisfiability evidence:
  at `kirovGenus X > 0` the atom is a THEOREM (Gate-A through the residue bridge), so the
  named hypothesis is the standard residue theorem, not a placeholder.
* `tailRiemannRoch_of_residueAtom` — `TailRiemannRoch X` from the atom (any genus).
* `h1Dim_zero_eq_zero_of_residueAtom` — **the G0 deliverable**: the `hga` atom
  `𝔘.h1Dim 0 = 0` at `kirovGenus X = 0`, conditional on the residue atom only.
* `exists_serreDualityData_of_genus_zero_of_residueAtom` — the keystone `g = 0` leg under
  the same single input.

Reference: Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5), Ch. VI; Forster,
*Lectures on Riemann Surfaces* (GTM 81), §17.4.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

namespace Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The named atom -/

/-- **The meromorphic-frame residue atom** (the single remaining analytic input of the G0
lane; `docs/planning/G0_BLOCKER.md` discharge shape 1): for the canonical frame `(ω₀, K)` of
the datum, the planar residue sum of `F·ω₀` vanishes over `supp(div F) ∪ supp K`, for every
global meromorphic `F`.  This is verbatim the `TailPairFrame.resSum` field at the canonical
slot family `slot p = formCoeff ω₀.toFun p`.

Mathematically TRUE on every compact Riemann surface (the residue theorem for meromorphic
1-forms, Forster §17.3 / Miranda Ch. VI); a THEOREM at `kirovGenus X > 0`
(`residueAtom_of_form` below, via Gate A).  At genus 0 it is the open analytic atom: the
Gate-A engine is parameterized by a HOLOMORPHIC `ω₀` and no factorization `F·ω₀ = α·g` with
`α` holomorphic exists at genus 0. -/
def CanonicalForm17Data.ResidueAtom (data : CanonicalForm17Data X) : Prop :=
  ∀ F : MeromorphicFunction X,
    ∑ p ∈ F.div.support ∪ data.K.support,
      planarCoeff (-1)
        (fun ζ => F.toFun ((chartAt (H := ℂ) p).symm ζ) * formCoeff data.ω₀.toFun p ζ)
        ((chartAt (H := ℂ) p) p) = 0

/-! ## The frame from a datum + its atom (genus-free) -/

/-- **The tail pair frame from a canonical datum and its residue atom.**  The slot family is
the coordinate coefficient `formCoeff ω₀.toFun p` of the datum's (meromorphic) frame form —
meromorphic at the chart centre by the form's own meromorphy, of exact order `K p` by the
datum's `order_eq`.  The residue field is the atom verbatim.  No genus hypothesis. -/
def TailPairFrame.ofResidueAtom (data : CanonicalForm17Data X)
    (hres : data.ResidueAtom) : TailPairFrame X where
  data := data
  slot := fun p => formCoeff data.ω₀.toFun p
  slot_mero := fun p => data.ω₀.meromorphic p
  slot_order := fun p => data.order_eq p
  resSum := hres

/-- Frame existence from the residue atom (genus-free). -/
theorem nonempty_tailPairFrame_of_residueAtom
    (h : ∃ data : CanonicalForm17Data X, data.ResidueAtom) :
    Nonempty (TailPairFrame X) := by
  obtain ⟨data, hres⟩ := h
  exact ⟨TailPairFrame.ofResidueAtom data hres⟩

/-! ## Satisfiability evidence: the atom is a THEOREM at positive genus -/

/-- **The residue atom holds for the holomorphic-form datum** (Gate A through the residue
bridge): for a nonzero holomorphic `α`, the datum `canonicalDataOfForm α hα` satisfies its
own residue atom — `resSum_planar` at the support `supp(div F) ∪ supp K`, with
`formCoeff (holToMero α).toFun p = coeffAt α p` definitionally. -/
theorem residueAtom_of_form (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    (canonicalDataOfForm α hα).ResidueAtom := by
  intro F
  have h := resSum_planar α F
    (S := F.div.support ∪ (canonicalDataOfForm α hα).K.support) Finset.subset_union_left
  rw [← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rfl

/-- At `kirovGenus X > 0` the residue atom is satisfiable — the named hypothesis of the G0
lane is the standard residue theorem, proven on the positive-genus side of the genus split. -/
theorem exists_residueAtom_of_kirovGenus_pos (hg : 0 < kirovGenus X) :
    ∃ data : CanonicalForm17Data X, data.ResidueAtom := by
  have hex : ∃ α : HolomorphicOneForms X, α ≠ 0 := by
    by_contra hcon
    push Not at hcon
    haveI hsub : Subsingleton (HolomorphicOneForms X) :=
      ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h0 : kirovGenus X = 0 := by
      unfold kirovGenus
      exact Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨α, hα⟩ := hex
  exact ⟨canonicalDataOfForm α hα, residueAtom_of_form α hα⟩

/-! ## The G0 deliverables: `TailRiemannRoch`, the `hga` atom, and the keystone `g = 0` leg -/

/-- **Tail Riemann–Roch from the residue atom** (any genus): the atom builds the frame, and
the frame-only tower (`TailPairFrame.pairingSurjective` → `TailPairFrame.tailRiemannRoch`)
does the rest. -/
theorem tailRiemannRoch_of_residueAtom (data : CanonicalForm17Data X)
    (hres : data.ResidueAtom) : TailRiemannRoch X :=
  (TailPairFrame.ofResidueAtom data hres).tailRiemannRoch

/-- **The G0 atom `hga` from the residue atom**: `h¹(𝒪) = 0` at `kirovGenus X = 0`, at any
locally realizable finite cover — the exact scalar input of
`exists_serreDualityData_of_arithmeticGenus_zero` (`G0_BLOCKER.md`), conditional on the
meromorphic-frame residue atom ONLY. -/
theorem h1Dim_zero_eq_zero_of_residueAtom (𝔘 : FiniteCover X) (hR : 𝔘.LocallyRealizable)
    (data : CanonicalForm17Data X) (hres : data.ResidueAtom) (hg0 : kirovGenus X = 0) :
    𝔘.h1Dim (0 : Divisor X) = 0 :=
  h1Dim_zero_eq_zero_of_kirovGenus_zero 𝔘 hR (tailRiemannRoch_of_residueAtom data hres) hg0

/-- The uniform genus identity `h¹(𝒪) = kirovGenus X` from the residue atom (any genus, any
locally realizable cover). -/
theorem h1Dim_zero_eq_kirovGenus_of_residueAtom (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (data : CanonicalForm17Data X) (hres : data.ResidueAtom) :
    𝔘.h1Dim (0 : Divisor X) = kirovGenus X :=
  h1Dim_zero_eq_kirovGenus_of_tailRR 𝔘 hR (tailRiemannRoch_of_residueAtom data hres)

/-- **The keystone `g = 0` leg from the residue atom**: `Nonempty (SerreDualityData 𝔘)` at
`kirovGenus X = 0`, with the `hga` scalar atom supplied by the tail tower under the single
named input. -/
theorem exists_serreDualityData_of_genus_zero_of_residueAtom (𝔘 : FiniteCover X)
    (hR : 𝔘.LocallyRealizable) (data : CanonicalForm17Data X) (hres : data.ResidueAtom)
    (hg0 : kirovGenus X = 0) :
    Nonempty (SerreDualityData 𝔘) :=
  exists_serreDualityData_of_genus_zero_of_tailRR 𝔘 hR
    (tailRiemannRoch_of_residueAtom data hres) hg0

/-! ## The genus-uniform frame split

Combining the unconditional positive-genus witness (`TailFrameWitness.lean`) with the atom
route: frame existence — hence `TailRiemannRoch X`, hence `h¹(𝒪) = g` at the canonical cover
— needs the residue atom only in the `kirovGenus X = 0` case. -/

/-- **The genus-split frame existence**: a tail pair frame exists given the residue atom in
the genus-0 case only (`kirovGenus X > 0` is covered by the holomorphic-form witness). -/
theorem nonempty_tailPairFrame_of_genus_split
    (h0 : kirovGenus X = 0 → ∃ data : CanonicalForm17Data X, data.ResidueAtom) :
    Nonempty (TailPairFrame X) := by
  rcases Nat.eq_zero_or_pos (kirovGenus X) with hg | hg
  · exact nonempty_tailPairFrame_of_residueAtom (h0 hg)
  · exact nonempty_tailPairFrame_of_kirovGenus_pos hg

/-- **The canonical-cover genus identity under the genus-split input**: `h¹(𝒪) = kirovGenus`
at the canonical chart-disk cover (the Layer-3 flip target), given the residue atom in the
genus-0 case only. -/
theorem h1Dim_zero_chartDiskCover_eq_kirovGenus_of_genus_split
    (h0 : kirovGenus X = 0 → ∃ data : CanonicalForm17Data X, data.ResidueAtom) :
    (chartDiskCover (X := X)).toFiniteCover.h1Dim (0 : Divisor X) = kirovGenus X := by
  obtain ⟨P⟩ := nonempty_tailPairFrame_of_genus_split h0
  exact h1Dim_zero_chartDiskCover_eq_kirovGenus_of_frame' P

/-! ## Down-payment toward the atom: exact differentials have zero planar residue

The first brick of every honest discharge route for `ResidueAtom` (`G0_BLOCKER.md`): the
order-`(−1)` planar coefficient of a DERIVATIVE vanishes — locally, `Res(dh) = 0` for any
meromorphic `h` (a Laurent series of the form `∑ aₖ·k·z^{k−1}` has no `z^{−1}` term).
One-variable, proven by the same leading-monomial stripping as the residue bridge. -/

/-- `deriv` is germ-local on the punctured filter: functions agreeing near `c` (off `c`)
have derivatives agreeing near `c` (off `c`). -/
theorem deriv_eventuallyEq_punctured {F G : ℂ → ℂ} {c : ℂ} (h : F =ᶠ[𝓝[≠] c] G) :
    deriv F =ᶠ[𝓝[≠] c] deriv G := by
  have h' : ∀ᶠ z in 𝓝 c, z ∈ ({c}ᶜ : Set ℂ) → F z = G z := eventually_nhdsWithin_iff.mp h
  obtain ⟨t, ht, htopen, hct⟩ := eventually_nhds_iff.mp h'
  refine eventually_nhdsWithin_iff.mpr
    (eventually_nhds_iff.mpr ⟨t, fun y hy hyne => ?_, htopen, hct⟩)
  refine Filter.EventuallyEq.deriv_eq ?_
  have hmem : t \ {c} ∈ 𝓝 y := (htopen.sdiff isClosed_singleton).mem_nhds ⟨hy, hyne⟩
  filter_upwards [hmem] with z hz
  exact ht z hz.1 hz.2

/-- The order-`≥ 0` base case: the derivative of an analytically-extendable germ has
nonnegative order, hence no residue. -/
theorem planarCoeff_neg_one_deriv_of_order_nonneg {H : ℂ → ℂ} {c : ℂ}
    (hH : MeromorphicAt H c) (h : 0 ≤ meromorphicOrderAt H c) :
    planarCoeff (-1) (deriv H) c = 0 := by
  have heq := hH.eq_nhdsNE_toMeromorphicNFAt
  have hNF : MeromorphicNFAt (toMeromorphicNFAt H c) c := meromorphicNFAt_toMeromorphicNFAt
  have hordeq : meromorphicOrderAt (toMeromorphicNFAt H c) c = meromorphicOrderAt H c :=
    (meromorphicOrderAt_congr heq).symm
  have hana : AnalyticAt ℂ (toMeromorphicNFAt H c) c :=
    hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 (hordeq ▸ h)
  have hdana : AnalyticAt ℂ (deriv (toMeromorphicNFAt H c)) c := hana.deriv
  rw [planarCoeff_congr (deriv_eventuallyEq_punctured heq) (-1)]
  refine planarCoeff_eq_zero_of_lt_order ?_ hdana.meromorphicAt
  refine lt_of_lt_of_le ?_ hdana.meromorphicOrderAt_nonneg
  exact_mod_cast (by norm_num : (-1 : ℤ) < 0)

/-- The bounded-depth case: at pole depth `≤ m`, the derivative has no residue.
Induction by leading-monomial stripping (the monomial derivatives
`a·n·(z−c)^{n−1}` never hit exponent `−1` for `n ≤ −1`). -/
private theorem planarCoeff_neg_one_deriv_of_le {c : ℂ} :
    ∀ m : ℕ, ∀ H : ℂ → ℂ, MeromorphicAt H c →
      ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H c →
      planarCoeff (-1) (deriv H) c = 0
  | 0, H, hH, hord => by
      refine planarCoeff_neg_one_deriv_of_order_nonneg hH ?_
      have h0 : ((-(0 : ℤ) : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) := by norm_num
      rw [← h0]
      simpa using hord
  | (m + 1), H, hH, hord => by
      set n : ℤ := -((m : ℤ) + 1) with hn
      have hordn : ((n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H c := by
        refine le_trans (le_of_eq ?_) hord
        rw [hn]
        push_cast
        ring_nf
      set a : ℂ := laurentCoeff n H c with ha
      by_cases ha0 : a = 0
      · -- bottom coefficient vanishes: the order is already `≥ −m`
        have hlt : ((n : ℤ) : WithTop ℤ) < meromorphicOrderAt H c :=
          (laurentCoeff_eq_zero_iff hH hordn).mp (by rw [← ha]; exact ha0)
        have hord' : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H c := by
          rcases eq_or_ne (meromorphicOrderAt H c) ⊤ with htop | hne
          · rw [htop]; exact le_top
          · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
            rw [← hv]
            rw [← hv] at hlt
            have hnv : n < v := by exact_mod_cast hlt
            have : -(m : ℤ) ≤ v := by omega
            exact_mod_cast this
        exact planarCoeff_neg_one_deriv_of_le m H hH hord'
      · -- strip the leading monomial
        set Mneg : ℂ → ℂ := fun z => -a * (z - c) ^ n with hMneg
        have hMnegm : MeromorphicAt Mneg c := meromorphicAt_monomial (-a) c n
        have hMnegord : meromorphicOrderAt Mneg c = (n : WithTop ℤ) :=
          meromorphicOrderAt_monomial (neg_ne_zero.mpr ha0) c n
        set G : ℂ → ℂ := H + Mneg with hG
        have hGm : MeromorphicAt G c := hH.add hMnegm
        have hordG : ((n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G c := by
          refine le_trans (le_min hordn (le_of_eq hMnegord.symm)) ?_
          exact meromorphicOrderAt_add hH hMnegm
        have hcoeffG : laurentCoeff n G c = 0 := by
          rw [hG, laurentCoeff_add hH hMnegm hordn (le_of_eq hMnegord.symm), ← ha,
            hMneg, laurentCoeff_monomial]
          ring
        have hltG : ((n : ℤ) : WithTop ℤ) < meromorphicOrderAt G c :=
          (laurentCoeff_eq_zero_iff hGm hordG).mp hcoeffG
        have hordG' : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G c := by
          rcases eq_or_ne (meromorphicOrderAt G c) ⊤ with htop | hne
          · rw [htop]; exact le_top
          · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
            rw [← hv]
            rw [← hv] at hltG
            have hnv : n < v := by exact_mod_cast hltG
            have : -(m : ℤ) ≤ v := by omega
            exact_mod_cast this
        have hIH : planarCoeff (-1) (deriv G) c = 0 :=
          planarCoeff_neg_one_deriv_of_le m G hGm hordG'
        set M : ℂ → ℂ := fun z => a * (z - c) ^ n with hM
        have hMm : MeromorphicAt M c := meromorphicAt_monomial a c n
        -- the derivative of the monomial, off the centre
        have hdM : ∀ z : ℂ, z ≠ c →
            HasDerivAt M (a * ((n : ℂ) * (z - c) ^ (n - 1))) z := by
          intro z hz
          have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
          have h1 : HasDerivAt (fun w : ℂ => w - c) 1 z := (hasDerivAt_id z).sub_const c
          have h2 : HasDerivAt (fun w : ℂ => w ^ n) ((n : ℂ) * (z - c) ^ (n - 1)) (z - c) :=
            hasDerivAt_zpow n (z - c) (Or.inl hzc)
          have h3 := (h2.comp z h1)
          rw [mul_one] at h3
          exact h3.const_mul a
        -- split `deriv H` as `deriv G + deriv M` off the centre
        have hHGM : H = fun z => G z + M z := by
          funext z
          rw [hG]
          simp only [Pi.add_apply, hMneg, hM]
          ring
        have hev : deriv H =ᶠ[𝓝[≠] c] deriv G + deriv M := by
          filter_upwards [hGm.eventually_analyticAt, self_mem_nhdsWithin] with z hzG hzc
          have hzc' : z ≠ c := by simpa using hzc
          have hdG : DifferentiableAt ℂ G z := hzG.differentiableAt
          have hdMz : DifferentiableAt ℂ M z := (hdM z hzc').differentiableAt
          show deriv H z = deriv G z + deriv M z
          rw [hHGM]
          exact deriv_add hdG hdMz
        have hdMev : deriv M =ᶠ[𝓝[≠] c] fun z => a * (n : ℂ) * (z - c) ^ (n - 1) := by
          filter_upwards [self_mem_nhdsWithin] with z hzc
          have hzc' : z ≠ c := by simpa using hzc
          rw [(hdM z hzc').deriv]
          ring
        have hMder_mero : MeromorphicAt (deriv M) c := by
          refine MeromorphicAt.congr (meromorphicAt_monomial (a * (n : ℂ)) c (n - 1)) ?_
          exact hdMev.symm
        have hMder0 : planarCoeff (-1) (deriv M) c = 0 := by
          rw [planarCoeff_congr hdMev, planarCoeff_monomial]
          have hne : (-1 : ℤ) ≠ n - 1 := by omega
          rw [if_neg hne]
        rw [planarCoeff_congr hev, planarCoeff_add (hGm.deriv) hMder_mero, hIH, hMder0,
          add_zero]

/-- **Exact meromorphic differentials have zero planar residue** (`Res(dh) = 0`, locally):
for `H` meromorphic at `c`, the order-`(−1)` planar coefficient of `deriv H` vanishes.
The local half of `∑Res(dh) = 0`; first brick of the `ResidueAtom` discharge routes. -/
theorem planarCoeff_neg_one_deriv {H : ℂ → ℂ} {c : ℂ} (hH : MeromorphicAt H c) :
    planarCoeff (-1) (deriv H) c = 0 := by
  rcases eq_or_ne (meromorphicOrderAt H c) ⊤ with htop | hne
  · have heq : H =ᶠ[𝓝[≠] c] (fun _ => (0 : ℂ)) := meromorphicOrderAt_eq_top_iff.mp htop
    rw [planarCoeff_congr (deriv_eventuallyEq_punctured heq) (-1)]
    have hd0 : deriv (fun _ : ℂ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
      funext z
      exact deriv_const z 0
    rw [hd0, planarCoeff_zero_fun]
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
    refine planarCoeff_neg_one_deriv_of_le (max 0 (-v)).toNat H hH ?_
    rw [← hv]
    have h1 : -(((max 0 (-v)).toNat : ℤ)) ≤ v := by omega
    exact_mod_cast h1

end Dolbeault

end Jacobians

end
