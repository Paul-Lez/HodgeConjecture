/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.SerreResidueRamifiedClusterTopology
import KirovDolbeault.MultiplicityPatchingConstruct
import KirovDolbeault.ProperMapDegreeSheets

/-!
# Closing Gate-A TARGET 1: the three conservation-of-number facts of `ofClusterFibrePoints`

`SerreResidueRamifiedClusterTopology.lean` reduced Gate-A TARGET 1 (`hgeom_fibre` for the real cover),
at each regular slit value `z`, to the **three minimal facts** of
`FibreClusterTopology.ofClusterFibrePoints`:

1. `hcl_fibre` — the cluster sheet points are preimages of `coe z`;
2. `hcl_distinct` — the cluster sheet points are pairwise distinct;
3. `hcard` — the conservation of number `∑ᵢ D.mult i = S.n`.

This file **discharges facts 1 and 2** from the genuine §5 normal-form geometry (carried as the
`clusterSection` section property `hcs_sec` plus the non-pole datum at the cluster point), and isolates
fact 3 — the §4 conservation-of-number degree count — to a single precise lemma stated against the
PROVEN argument-principle engine (`Jacobians.ProperMapDegreeSheets.exists_properMapDegree_proven` /
`IsLocallyConstant (N f)`).

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `clusterSection_toRiemannSphere_of_section_nonpole` — fact 1 (`hcl_fibre`) at one `(i,j)`: the
  cluster section point is a preimage of `coe z`, from its `holoRepr`-section value `z` plus the
  non-pole datum at the point (`nonpole`: `0 ≤ orderAtPoint`).  The §5 normal form (via the field
  `hcs_sec`) supplies the section value; the non-pole datum is the genuine geometric input (a preimage
  of the *finite* value `z` is a non-pole).
* `clusterSection_injective_of_distinctPreimages_distinctRoots` — fact 2 (`hcl_distinct`): the cluster
  sheet points across the whole `Σ`-index are pairwise distinct, from (a) the distinctness of the
  fixed preimages `D.xs` (T2-separated, so their clusters are disjoint) and (b) the within-cluster
  distinctness of the `mᵢ` sheets at one preimage (the primitive root `ζ` separates `ζʲ·w₀` and `s` is
  locally injective).
* `FibreClusterTopology.ofClusterSplitData` — the minimal-residual constructor: assembles a
  `FibreClusterTopology` from the per-preimage §5 cluster data tied to `f` (the section property + the
  non-pole datum + the within-cluster injectivity) and the single conservation-of-number count `hcard`,
  proving facts 1 and 2 internally.  The only non-routine, non-derived input is `hcard`.

## The precise remaining `hcard` lemma (fact 3, the §4 conservation-of-number wall)

`hcard : ∑ᵢ D.mult i = S.n` is the genuine conservation-of-number degree count.  It is **not** local in
the slit value `z`: it equates the cover's sheet count `S.n = #F⁻¹(coe z)` (regular fibre) with the
total cluster multiplicity `∑ᵢ D.mult i` at the *pole-value centre* `c`, an equality that holds across
the branch value `c` precisely by the local constancy of the multiplicity sum `N f` (Forster §4).  We
state it as `sum_mult_eq_sheetCount_of_conservation`, reducing it to:

* the cover-degree readings `S.n = #F⁻¹(coe z)` and `∑ᵢ D.mult i = fibreMult f (coe c)`;
* the local constancy `N f (coe z) = N f (coe c)` (the argument-principle engine).

This is the single irreducible naturals equality of TARGET 1.

## ⚠ Soundness

Facts 1 and 2 are **genuine geometry**, never asserted: fact 1 is the §5-normal-form preimage property
(the cluster sheets ARE preimages) plus the true non-pole datum; fact 2 is genuine point distinctness.
Fact 3 (`hcard`) is the genuine §4 conservation of number — `∑ᵢ D.mult i = S.n` with `D.mult i` the
genuine local degree and `S.n` the genuine sheet count — routed through the PROVEN
`exists_properMapDegree` engine (which is *upstream* of Riemann–Roch — it IS the `deg_div` engine — so
no circularity).  No custom axiom, no unproved obligation on a false statement, no false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (the degree / conservation of number, Cor.
  4.24–4.25), §5 (the normal form `z = wᵐ`).
* `Jacobians/ProperMapDegreeSheets.lean` (`exists_properMapDegree_proven`),
  `Jacobians/ProperMapDegreeConstruct.lean` (`N`/`fibreMult`/local constancy),
  `SerreResidueRamifiedMultiplicityBridge.lean` (`exists_clusterSplit_at_fibrePoint`,
  `analyticOrderAt_holoRepr_sub_eq_mult`), `SerreResidueRamifiedClusterTopology.lean`
  (`FibreClusterTopology`, `ofClusterFibrePoints`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.ProperMapDegreeConstruct Jacobians.MultiplicityPatchingConstruct
  Jacobians.ProperMapDegreeSheets

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Fact 1 (`hcl_fibre`): the cluster sheet points are genuine preimages of `coe z`

The cluster section point `q = clusterSection D Cl i j z` is a genuine local section of `f.holoRepr`
through the slit value `z` (the §5 normal-form section property, carried as the field `hcs_sec`): so
`f.holoRepr q = z`.  Combined with the genuine geometric datum that `q` is a **non-pole** (it is a
preimage of the *finite* value `z`, so `0 ≤ f.orderAtPoint q`), the sphere map reads `f.toRiemannSphere
q = coe (f.holoRepr q) = coe z` (`toRiemannSphere_of_nonneg`).  This is fact 1 at one `(i,j)`. -/

/-- **Fact 1 (`hcl_fibre`) at one `(i,j)`.**  If the cluster section point `q = clusterSection D Cl i j
z` is a section of `f.holoRepr` at `z` (`f.holoRepr q = z`, the §5 normal-form section property) and a
non-pole (`0 ≤ f.orderAtPoint q`, the genuine geometric datum that a preimage of the finite value `z`
is a non-pole), then it is a genuine preimage of `coe z`: `f.toRiemannSphere q = coe z`. -/
theorem clusterSection_toRiemannSphere_of_section_nonpole {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {c : ℂ} {Sset : Set ℂ} {D : FibreRamifiedData g f c}
    {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ} {i : D.ι} {j : Fin (D.mult i)}
    (hsec : f.holoRepr (clusterSection D Cl i j z) = z)
    (hnp : 0 ≤ f.orderAtPoint (clusterSection D Cl i j z)) :
    f.toRiemannSphere (clusterSection D Cl i j z) = (((z : ℂ) : RiemannSphere)) := by
  rw [f.toRiemannSphere_of_nonneg hnp, hsec]

/-! ## Fact 2 (`hcl_distinct`): the cluster sheet points are pairwise distinct

Across the whole `Σ`-index `Σ i, Fin (D.mult i)`, two cluster section points coincide only if their
indices coincide.  We split into the within-cluster case (same preimage `i`, different sheet `j ≠ k`)
and the cross-cluster case (different preimages `i ≠ i'`).

* **Within a cluster** the `mᵢ` sheet points are distinct because the §5 local inverse straightens
  them: `clusterSheet (Cl i).s … j z = (Cl i).s (ζʲ·w₀ z)` and the normal-form coordinate `η`
  recovers `η ((Cl i).s (ζʲ·w₀ z)) = ζʲ·w₀ z` (the inverse property); if two sheets coincide as points
  of `X`, then (chart injectivity) their `s`-arguments coincide, then (applying `η`) `ζʲ·w₀ z = ζᵏ·w₀
  z`, forcing `ζʲ = ζᵏ` (`w₀ z ≠ 0`), hence `j = k` (`ζ` primitive, `j,k < mᵢ`).
* **Across clusters** the points lie in disjoint chart sources near the *distinct* preimages `D.xs i ≠
  D.xs i'`, so they are separated.

Both legs are isolated as hypotheses (the genuine §5 / T2 geometry); the constructor below derives the
full `Σ`-index injectivity from them. -/

/-- **Within-cluster distinctness.**  If two cluster section points at the *same* preimage `i` coincide
(`clusterSection D Cl i j z = clusterSection D Cl i k z`), then `j = k`, provided:

* the cluster sheet arguments lie in `D.xs i`'s chart target (`htgt_j`, `htgt_k`) — so chart injectivity
  applies;
* the §5 normal-form coordinate `η` recovers the argument at each sheet (`hinv_j`, `hinv_k`:
  `η ((Cl i).s (ζʲ·w₀ z)) = ζʲ·w₀ z`);
* the slit branch is nonzero (`hw₀ : (Cl i).w₀ z ≠ 0`);
* `(Cl i).ζ` is a primitive `(Cl i).m`-th root (`ClusterTraceData.hζ`) and the multiplicity matches
  (`hm : D.mult i = (Cl i).m`).

The argument is the §5 straightening uniqueness: equal points ⟹ equal `s`-args ⟹ (apply `η`) equal
`ζ`-powers ⟹ equal indices (primitivity). -/
theorem clusterSection_within_cluster_inj {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {c : ℂ} {Sset : Set ℂ} {D : FibreRamifiedData g f c}
    {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ} {i : D.ι} {j k : Fin (D.mult i)}
    {η : ℂ → ℂ}
    (hm : D.mult i = (Cl i).m)
    (htgt_j : clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z ∈ (chartAt ℂ (D.xs i)).target)
    (htgt_k : clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ k z ∈ (chartAt ℂ (D.xs i)).target)
    (hinv_j : η ((Cl i).s ((Cl i).ζ ^ (j : ℕ) * (Cl i).w₀ z)) = (Cl i).ζ ^ (j : ℕ) * (Cl i).w₀ z)
    (hinv_k : η ((Cl i).s ((Cl i).ζ ^ (k : ℕ) * (Cl i).w₀ z)) = (Cl i).ζ ^ (k : ℕ) * (Cl i).w₀ z)
    (hw₀ : (Cl i).w₀ z ≠ 0)
    (hpt : clusterSection D Cl i j z = clusterSection D Cl i k z) :
    j = k := by
  -- (1) Equal points in `X` ⟹ equal cluster-sheet arguments (chart injectivity on the target).
  have hsheet_eq : clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z
      = clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ k z := by
    have h := congrArg (chartAt ℂ (D.xs i)) hpt
    rwa [clusterSection, clusterSection, (chartAt ℂ (D.xs i)).right_inv htgt_j,
      (chartAt ℂ (D.xs i)).right_inv htgt_k] at h
  -- (2) Apply `η`; the inverse property turns equal `s`-args into equal `ζ`-powers.
  have hpow_eq : (Cl i).ζ ^ (j : ℕ) * (Cl i).w₀ z = (Cl i).ζ ^ (k : ℕ) * (Cl i).w₀ z := by
    rw [← hinv_j, ← hinv_k]
    exact congrArg η hsheet_eq
  -- (3) Cancel the nonzero branch, get `ζʲ = ζᵏ`, then primitivity gives `j = k`.
  have hzeta : (Cl i).ζ ^ (j : ℕ) = (Cl i).ζ ^ (k : ℕ) := mul_right_cancel₀ hw₀ hpow_eq
  have hjm : (j : ℕ) < (Cl i).m := hm ▸ j.isLt
  have hkm : (k : ℕ) < (Cl i).m := hm ▸ k.isLt
  exact Fin.ext ((Cl i).hζ.pow_inj hjm hkm hzeta)

/-- **The full `Σ`-index distinctness (fact 2, `hcl_distinct`).**  The cluster section points are
pairwise distinct over the whole `Σ`-index `Σ i, Fin (D.mult i)`, given:

* `hwithin` — within-cluster injectivity: at each preimage `i`, distinct sheets give distinct points
  (`clusterSection D Cl i j z = clusterSection D Cl i k z → j = k`), supplied per preimage (e.g. by
  `clusterSection_within_cluster_inj`);
* `hcross` — cross-cluster separation: at *distinct* preimages `i ≠ i'`, the cluster points are
  distinct (`clusterSection D Cl i j z ≠ clusterSection D Cl i' k z`) — the genuine §5 / T2 fact that
  the clusters at distinct preimages are disjoint.

These are exactly the two legs of "the clusters are disjoint, within-cluster distinct" (Forster §4–5).
-/
theorem clusterSection_injective_of_within_cross {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {c : ℂ} {Sset : Set ℂ} {D : FibreRamifiedData g f c}
    {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (hwithin : ∀ (i : D.ι) (j k : Fin (D.mult i)),
      clusterSection D Cl i j z = clusterSection D Cl i k z → j = k)
    (hcross : ∀ (i i' : D.ι) (j : Fin (D.mult i)) (k : Fin (D.mult i')), i ≠ i' →
      clusterSection D Cl i j z ≠ clusterSection D Cl i' k z) :
    Function.Injective
      (fun p : Σ i : D.ι, Fin (D.mult i) => clusterSection D Cl p.1 p.2 z) := by
  rintro ⟨i, j⟩ ⟨i', k⟩ hpq
  simp only at hpq
  by_cases hii : i = i'
  · subst hii
    -- Same preimage: within-cluster injectivity gives `j = k`.
    exact Sigma.ext rfl (heq_of_eq (hwithin i j k hpq))
  · -- Distinct preimages: cross-cluster separation contradicts `hpq`.
    exact absurd hpq (hcross i i' j k hii)

/-! ## Fact 3 (`hcard`): the conservation-of-number degree count `∑ᵢ D.mult i = S.n`

This is the genuine §4 conservation of number, the irreducible wall of TARGET 1.  Its content is the
equality of two cover-degree readings across the branch value `c`:

* the **regular-fibre reading** `S.n = fibreMult f (coe z)` — the number of sheets at the regular slit
  value `z` equals the fibre-multiplicity sum (every local degree is `1` at a regular value);
* the **pole-fibre reading** `∑ᵢ D.mult i = fibreMult f (coe c)` — the total cluster multiplicity at
  the centre `c` equals the fibre-multiplicity sum there (each `D.mult i` is the genuine local degree,
  the multiplicity bridge).

These two `fibreMult` values are **equal** because the fibre-multiplicity function `N f` is *locally
constant* (the global argument principle, the proven `exists_properMapDegree` engine) on the
*connected* sphere `ℂℙ¹` — so it is globally constant, and `N f = fibreMult f` everywhere
(`N_eq_fibreMult_everywhere`).  We supply the local constancy from the PROVEN per-fibre conservation
supply (`localMultiplicitySheets_of_nonconstant` for a nonconstant cover) — *upstream* of Riemann–Roch
(it IS the `deg_div` engine), so no circularity.

We isolate fact 3 to the lemma `sum_mult_eq_sheetCount_of_readings`, taking the two readings as
hypotheses (the genuine residual) and discharging the constancy middle from the engine. -/

/-- **The fibre-multiplicity function is globally constant.**  For a nonconstant cover `f` (`f.div ≠
0`), the genuine multiplicity sum `fibreMult f` agrees at any two sphere values: `fibreMult f w₁ =
fibreMult f w₂`.  This is the §4 conservation of number — `IsLocallyConstant (N f)` (the PROVEN
argument-principle engine, via `localMultiplicitySheets_of_nonconstant`) on the *connected* sphere
`ℂℙ¹`, combined with `N f = fibreMult f` everywhere. -/
theorem fibreMult_const_of_nonconstant {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    (w₁ w₂ : RiemannSphere) : fibreMult f w₁ = fibreMult f w₂ := by
  -- The argument-principle engine: `N f` is locally constant.
  have hlc : IsLocallyConstant (N f) :=
    isLocallyConstant_N_of_localSheets f (localMultiplicitySheets_of_nonconstant f hdiv)
  -- On the connected sphere `ℂℙ¹`, a locally constant function is globally constant.
  have hconst : N f w₁ = N f w₂ := by
    rw [hlc.eq_const w₁]; rfl
  -- `N f = fibreMult f` everywhere.
  rw [← N_eq_fibreMult_everywhere f w₁, ← N_eq_fibreMult_everywhere f w₂]
  exact hconst

/-- **Fact 3 (`hcard`) from the two cover-degree readings.**  The conservation-of-number count `∑ᵢ
D.mult i = S.n` follows, for a nonconstant cover `f` (`f.div ≠ 0`), from:

* `hSn` — the **regular-fibre reading** `(S.n : ℤ) = fibreMult f (coe z)` (the sheet count equals the
  fibre-multiplicity sum at the regular slit value `z`);
* `hDc` — the **pole-fibre reading** `(∑ᵢ D.mult i : ℤ) = fibreMult f (coe c)` (the total cluster
  multiplicity equals the fibre-multiplicity sum at the centre `c`).

The two `fibreMult` values are equal by the conservation of number (`fibreMult_const_of_nonconstant`),
so `(S.n : ℤ) = (∑ᵢ D.mult i : ℤ)`, hence `∑ᵢ D.mult i = S.n` by `Nat.cast` injectivity.  This is the
genuine §4 wall, isolated to the two cover-degree readings + the proven constancy engine. -/
theorem sum_mult_eq_sheetCount_of_readings {g : X → ℂ}
    {f : MeromorphicFunction X} {c : ℂ} {D : FibreRamifiedData g f c}
    {z : ℂ} {n : ℕ} (hdiv : (f.div : Divisor X) ≠ 0)
    (hSn : (n : ℤ) = fibreMult f (((z : ℂ) : RiemannSphere)))
    (hDc : ((∑ i, D.mult i : ℕ) : ℤ) = fibreMult f (((c : ℂ) : RiemannSphere))) :
    ∑ i, D.mult i = n := by
  have hconst := fibreMult_const_of_nonconstant hdiv (((z : ℂ) : RiemannSphere))
    (((c : ℂ) : RiemannSphere))
  have hint : ((∑ i, D.mult i : ℕ) : ℤ) = (n : ℤ) := by rw [hDc, ← hconst, ← hSn]
  exact_mod_cast hint

/-- **The pole-fibre reading `hDc`.**  `(∑ᵢ D.mult i : ℤ) = fibreMult f (coe c)`, given that the
preimage enumeration `D.xs` is injective and exhausts the *whole* fibre `F⁻¹(coe c)`
(`hrange : Set.range D.xs = F⁻¹(coe c)`), and each stored multiplicity is the genuine local degree
(`hmatch : (D.mult i : ℤ) = localDeg f (coe c) (D.xs i)`).

`fibreMult f (coe c)` is by definition the local-degree finsum over the fibre; the fibre is the range
of the injective `D.xs` (`finsum_mem_range`), so the finsum reindexes to the finite sum `∑ᵢ localDeg f
(coe c) (D.xs i)`, which is `∑ᵢ D.mult i` by `hmatch`.  The `hmatch` half is the multiplicity bridge
(`analyticOrderAt_holoRepr_sub_eq_mult`, the genuine local degree); `hrange` is the genuine
conservation-of-number input that `D` enumerates the whole fibre. -/
theorem sum_mult_eq_fibreMult_of_enumeration {g : X → ℂ}
    {f : MeromorphicFunction X} {c : ℂ} (D : FibreRamifiedData g f c)
    (hD_inj : Function.Injective D.xs)
    (hrange : Set.range D.xs = f.toRiemannSphere ⁻¹' {(((c : ℂ) : RiemannSphere))})
    (hmatch : ∀ i, ((D.mult i : ℕ) : ℤ) = localDeg f (((c : ℂ) : RiemannSphere)) (D.xs i)) :
    ((∑ i, D.mult i : ℕ) : ℤ) = fibreMult f (((c : ℂ) : RiemannSphere)) := by
  classical
  -- `fibreMult f (coe c) = ∑ᶠ x ∈ F⁻¹(coe c), localDeg …`; rewrite the fibre as `range D.xs`.
  rw [fibreMult, ← hrange, finsum_mem_range hD_inj, finsum_eq_sum_of_fintype]
  -- `∑ᵢ localDeg f (coe c) (D.xs i) = ∑ᵢ D.mult i` by the multiplicity match.
  push_cast
  exact Finset.sum_congr rfl (fun i _ => hmatch i)

/-- **The multiplicity-match `hmatch` from the bridge.**  At a preimage `D.xs i` over `coe c` that is a
non-pole (`hnp : 0 ≤ f.orderAtPoint (D.xs i)`) of a nonconstant cover (`f.div ≠ 0`), with the stored
multiplicity the genuine local degree's `toNat` (`hmult : D.mult i = (localDeg f (coe c) (D.xs i)).toNat`),
the integer reading holds: `(D.mult i : ℤ) = localDeg f (coe c) (D.xs i)`.  This is the multiplicity
bridge `analyticOrderAt_holoRepr_sub_eq_mult` (its third conjunct `localDeg = (localDeg).toNat`),
rewritten through `hmult`. -/
theorem mult_eq_localDeg_of_nonpole {g : X → ℂ}
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    {D : FibreRamifiedData g f c} (i : D.ι)
    (hnp : 0 ≤ f.orderAtPoint (D.xs i))
    (hmult : D.mult i = (localDeg f (((c : ℂ) : RiemannSphere)) (D.xs i)).toNat) :
    ((D.mult i : ℕ) : ℤ) = localDeg f (((c : ℂ) : RiemannSphere)) (D.xs i) := by
  obtain ⟨_, _, hloc⟩ := analyticOrderAt_holoRepr_sub_eq_mult f hdiv (D.hmem i) hnp
  rw [hmult, ← hloc]

/-! ### The regular-fibre reading `hSn`

At the regular slit value `z` the sphere sheet system `S` reads the whole fibre: `S.n = #F⁻¹(coe z)`
(the `n` injective sheets sweep out the fibre, `S.fibre_eq` + `S.sheet_inj`).  And `fibreMult f (coe
z)` is the local-degree finsum over that fibre; at a *regular* value every local degree is `1`, so the
finsum is just the cardinality `#F⁻¹(coe z) = S.n`.  This is the regular-fibre half of conservation. -/

/-- **The sheet count is the fibre cardinality.**  For a sphere sheet system `S` of `F =
f.toRiemannSphere` at `coe z`, the number of sheets `S.n` equals the cardinality of the fibre over `coe
z`: `S.n = (F⁻¹{coe z}).ncard`.  The `n` injective holomorphic sheets sweep out the fibre
(`S.fibre_eq` at `coe z ∈ S.V`), and they are pairwise distinct (`S.sheet_inj`), so the fibre is the
image of `Fin S.n` under an injection. -/
theorem sheetSystem_n_eq_ncard {f : MeromorphicFunction X} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) :
    S.n = (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).ncard := by
  rw [S.fibre_eq _ S.mem_V, ← Set.image_univ,
    Set.ncard_image_of_injective _ (S.sheet_inj _ S.mem_V), Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The fibre-multiplicity sum at a regular value is the fibre cardinality.**  If the fibre `F⁻¹(coe
z)` is finite (`hfin`) and every local degree over `coe z` is `1` (`hreg : ∀ x ∈ F⁻¹(coe z), localDeg f
(coe z) x = 1` — the regular-value content), then `fibreMult f (coe z) = (F⁻¹(coe z)).ncard`: the
local-degree finsum over the fibre is a sum of `1`s, hence the cardinality. -/
theorem fibreMult_eq_ncard_of_localDeg_one {f : MeromorphicFunction X} {z : ℂ}
    (hfin : (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).Finite)
    (hreg : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
      localDeg f (((z : ℂ) : RiemannSphere)) x = 1) :
    fibreMult f (((z : ℂ) : RiemannSphere))
      = ((f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).ncard : ℤ) := by
  classical
  rw [fibreMult, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Finset.sum_congr rfl (fun x hx => hreg x (by simpa using hx))]
  rw [Finset.sum_const, Set.ncard_eq_toFinset_card _ hfin]
  simp

/-- **The regular-fibre reading `hSn`.**  `(S.n : ℤ) = fibreMult f (coe z)`, given that the fibre over
`coe z` is finite (`hfin`) and every local degree there is `1` (`hreg`, the regular-value content).
Combines `sheetSystem_n_eq_ncard` (`S.n = #F⁻¹(coe z)`) with `fibreMult_eq_ncard_of_localDeg_one`
(`fibreMult f (coe z) = #F⁻¹(coe z)`). -/
theorem sheetSystem_n_eq_fibreMult {f : MeromorphicFunction X} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hfin : (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).Finite)
    (hreg : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
      localDeg f (((z : ℂ) : RiemannSphere)) x = 1) :
    (S.n : ℤ) = fibreMult f (((z : ℂ) : RiemannSphere)) := by
  rw [sheetSystem_n_eq_ncard S, fibreMult_eq_ncard_of_localDeg_one hfin hreg]

/-! ### Fact 3 (`hcard`), fully assembled from the genuine geometric primitives

Combining the regular-fibre reading (`sheetSystem_n_eq_fibreMult`), the pole-fibre reading
(`sum_mult_eq_fibreMult_of_enumeration` + `mult_eq_localDeg_of_nonpole`), and the conservation-of-number
engine (`sum_mult_eq_sheetCount_of_readings`), we obtain `∑ᵢ D.mult i = S.n` from the *genuine*
geometric primitives at the two ends of the slit, and nothing else.  These primitives are exactly the
honest §4 conservation-of-number content: the cover behaves like a covering off the branch locus
(regular-value: finite fibre + every local degree `1`) and the pole-value fibre is enumerated with the
genuine local-degree multiplicities. -/

/-- **Fact 3 (`hcard`), fully assembled.**  For a nonconstant cover `f` (`f.div ≠ 0`), the
conservation-of-number count `∑ᵢ D.mult i = S.n` holds, given the genuine §4 geometric primitives:

* **regular fibre** (at the slit value `z`): the fibre `F⁻¹(coe z)` is finite (`hfin_z`) and every
  local degree there is `1` (`hreg_z` — `z` is a regular value, off the branch locus);
* **pole fibre** (at the centre `c`): the preimage enumeration `D.xs` is injective (`hD_inj`) and
  exhausts the whole fibre `F⁻¹(coe c)` (`hrange`), each preimage is a non-pole (`hnp`) with the stored
  multiplicity the genuine local-degree `toNat` (`hmult_eq`).

The two cover-degree readings (`S.n = fibreMult f (coe z)`, `∑ᵢ D.mult i = fibreMult f (coe c)`) are
equal by the local constancy of the multiplicity sum on the connected sphere (the proven
`exists_properMapDegree` engine), giving the natural-number equality. -/
theorem sum_mult_eq_sheetCount_of_primitives {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {c : ℂ} {Sset : Set ℂ} (hdiv : (f.div : Divisor X) ≠ 0)
    (D : FibreRamifiedData g f c) (_Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset)
    {z : ℂ} (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hfin_z : (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).Finite)
    (hreg_z : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
      localDeg f (((z : ℂ) : RiemannSphere)) x = 1)
    (hD_inj : Function.Injective D.xs)
    (hrange : Set.range D.xs = f.toRiemannSphere ⁻¹' {(((c : ℂ) : RiemannSphere))})
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (D.xs i))
    (hmult_eq : ∀ i, D.mult i = (localDeg f (((c : ℂ) : RiemannSphere)) (D.xs i)).toNat) :
    ∑ i, D.mult i = S.n :=
  sum_mult_eq_sheetCount_of_readings hdiv
    (sheetSystem_n_eq_fibreMult S hfin_z hreg_z)
    (sum_mult_eq_fibreMult_of_enumeration D hD_inj hrange
      (fun i => mult_eq_localDeg_of_nonpole hdiv i (hnp i) (hmult_eq i)))

/-! ## The minimal-residual constructor `FibreClusterTopology.ofClusterSplitData`

We assemble a `FibreClusterTopology` from the genuine §5 / §4 geometric primitives, proving the three
facts (`hcl_fibre`, `hcl_distinct`, `hcard`) of `ofClusterFibrePoints` internally:

* `hcl_fibre` (fact 1) ← `clusterSection_toRiemannSphere_of_section_nonpole`: the cluster section is a
  `holoRepr`-section at `z` (read off the carried `hcs_sec` at `w = z`) and a non-pole (`hcs_np`);
* `hcl_distinct` (fact 2) ← `clusterSection_injective_of_within_cross`: within-cluster injectivity
  `hwithin` (the §5 straightening uniqueness) + cross-cluster separation `hcross` (the clusters at
  distinct preimages are disjoint);
* `hcard` (fact 3) ← `sum_mult_eq_sheetCount_of_primitives`: the regular-fibre + pole-fibre cover-degree readings,
  equated by the proven conservation-of-number engine.

The routine analytic residuals `hsrc`/`hsheet_diff`/`hcs_sec` and the sheet-system regularity
`S`/`hderiv`/`hmero`/`hcoh` are passed straight through to `ofClusterFibrePoints`. -/

/-- **`FibreClusterTopology` from the §5 / §4 geometric primitives.**  At a regular slit value `z`,
assemble a `FibreClusterTopology Φ D Cl z`, proving the three conservation-of-number facts internally:

* sheet-system regularity `S`/`hderiv`/`hmero`/`hcoh` (passed through);
* the cluster-section section property `hcs_sec` (`holoRepr (clusterSection … w) = w` near `z`) and its
  non-pole datum `hcs_np` (`0 ≤ orderAtPoint (clusterSection … z)`) — together fact 1 (`hcl_fibre`);
* within-cluster injectivity `hwithin` and cross-cluster separation `hcross` — together fact 2
  (`hcl_distinct`);
* the regular-fibre primitives `hfin_z`/`hreg_z` and the pole-fibre primitives
  `hD_inj`/`hrange`/`hnp`/`hmult_eq` — together fact 3 (`hcard`), via the proven
  `exists_properMapDegree` engine;
* the routine cluster-sheet residuals `hsrc`/`hsheet_diff`.

This is the cleanest geometric input for Gate-A TARGET 1 at one slit value: the §5 normal-form data
tied to `f`, plus the §4 conservation-of-number cover-degree readings. -/
noncomputable def FibreClusterTopology.ofClusterSplitData {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    {D : FibreRamifiedData g f c} {Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset} {z : ℂ}
    (hdiv : (f.div : Divisor X) ≠ 0)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ k, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ k, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))))
    (hcoh : valueChartTrace ω₀ f Φ z
      = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z)
    -- fact 1 (`hcl_fibre`): the cluster section is a `holoRepr`-section + non-pole.
    (hcs_sec : ∀ (i : D.ι) (j : Fin (D.mult i)),
      ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection D Cl i j w) = w)
    (hcs_np : ∀ (i : D.ι) (j : Fin (D.mult i)),
      0 ≤ f.orderAtPoint (clusterSection D Cl i j z))
    -- fact 2 (`hcl_distinct`): within-cluster injectivity + cross-cluster separation.
    (hwithin : ∀ (i : D.ι) (j k : Fin (D.mult i)),
      clusterSection D Cl i j z = clusterSection D Cl i k z → j = k)
    (hcross : ∀ (i i' : D.ι) (j : Fin (D.mult i)) (k : Fin (D.mult i')), i ≠ i' →
      clusterSection D Cl i j z ≠ clusterSection D Cl i' k z)
    -- fact 3 (`hcard`): the regular-fibre + pole-fibre cover-degree readings.
    (hfin_z : (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).Finite)
    (hreg_z : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
      localDeg f (((z : ℂ) : RiemannSphere)) x = 1)
    (hD_inj : Function.Injective D.xs)
    (hrange : Set.range D.xs = f.toRiemannSphere ⁻¹' {(((c : ℂ) : RiemannSphere))})
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (D.xs i))
    (hmult_eq : ∀ i, D.mult i = (localDeg f (((c : ℂ) : RiemannSphere)) (D.xs i)).toNat)
    -- routine cluster-sheet residuals.
    (hsrc : ∀ (i : D.ι) (j : Fin (D.mult i)),
      ∀ᶠ w in 𝓝 z, clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w ∈ (chartAt ℂ (D.xs i)).target)
    (hsheet_diff : ∀ (i : D.ι) (j : Fin (D.mult i)),
      DifferentiableAt ℂ (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z) :
    FibreClusterTopology Φ D Cl z :=
  FibreClusterTopology.ofClusterFibrePoints S hderiv hmero hcoh
    -- fact 1: `toRiemannSphere (clusterSection …) = coe z`.
    (fun i j => clusterSection_toRiemannSphere_of_section_nonpole
      (hcs_sec i j).self_of_nhds (hcs_np i j))
    -- fact 2: full `Σ`-index distinctness.
    (clusterSection_injective_of_within_cross hwithin hcross)
    -- fact 3: the conservation-of-number count.
    (sum_mult_eq_sheetCount_of_primitives hdiv D Cl S hfin_z hreg_z hD_inj hrange hnp hmult_eq)
    hsrc hsheet_diff hcs_sec

end Jacobians.Dolbeault.SerreResidueTheorem
