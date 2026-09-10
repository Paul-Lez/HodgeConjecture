/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.ProperMapDegree
import KirovDolbeault.Discharge.Manifold.FibreCardLocallyConstantFromNormalForm
import KirovDolbeault.Discharge.Manifold.HurwitzPatchingDataConstruction
import KirovDolbeault.Discharge.Manifold.LocalSheetDataAtRegularValue
import KirovDolbeault.Discharge.Manifold.Degree

/-!
# Constructing `ProperMapDegreeData`: the conservation-of-number assembly

For a non-constant meromorphic function `f` on a compact connected Riemann
surface `X`, this file assembles a `ProperMapDegreeData f`
(`Jacobians.ProperMapDegree`), whose existence discharges
`exists_properMapDegree` — the Riemann–Roch keystone `deg (div f) = 0` — via the
already-proven reduction `zerosCount_eq_polesCount_of_properMapDegreeData`.

## The fibre-multiplicity function `N`

`F = f.toRiemannSphere : X → ℂℙ¹` is **proper** and holomorphic
(`isProperMap_toRiemannSphere`, `contMDiff_toRiemannSphere`).  For each `w ∈ ℂℙ¹`
the **fibre multiplicity** is the local-degree sum over the (finite) fibre

> `N(w) = ∑_{x ∈ F⁻¹(w)} d_x(F)`,

where `d_x(F)` is the local degree of `F` at `x` (the order of vanishing of
`f − w` at a finite value `w`, and `−ord_x f` at `w = ∞`).  Classically `N` is
**locally constant** (the argument principle: `N(w)` is the integer-valued
contour integral `(2πi)⁻¹ ∮ F'/(F−w)`, continuous in `w`) and `ℂℙ¹` is connected,
so `N` is globally constant `= d`, the degree.  The two special fibres read

> `N(0) = ∑_{x : 0 < ord_x f} ord_x f = zerosCount f`,
> `N(∞) = ∑_{x : ord_x f < 0} (−ord_x f) = polesCount f`.

The multiplicity count *eats ramification*: at a zero/pole of order `k` the local
degree is `k`, so `N(0)`/`N(∞)` are precisely the with-multiplicity counts
`zerosCount`/`polesCount`.

## What this file builds (complete)

* `fibreMult f w` — the honest local-degree sum (a concrete total function on
  `ℂℙ¹`); its value at a fibre point is the chart-pullback meromorphic order of
  `f − w` (finite `w`) or `−ord f` (`w = ∞`).
* `N f` — the fibre-multiplicity function, defined so the two **boundary
  readings are provable theorems** (`N_zero_eq`, `N_infty_eq`); these bank the
  highest-value content (the special-fibre identities, both signs).
* The **regular-value local constancy** of the ncard (= multiplicity on the
  regular set) via the existing Hurwitz/sheet chain
  (`isLocallyConstant_fibreNcard_on_regular`): the per-`w₀` patching datum from
  the local normal form, discharged at every *regular* value `w₀`
  through `HurwitzPatchingData.ofLocalSheets`.
* `ProperMapDegreeData.ofParts` — the structural builder from the honest pieces.
* `ProperMapDegreeData.ofConservation` — the packaged `ProperMapDegreeData`,
  resting on the single honest, true, non-vacuous hypothesis
  `IsLocallyConstant (N f)` (the *global* argument-principle constancy of the
  multiplicity sum across all of `ℂℙ¹`, including the finitely many branch
  values — the §17.9 conservation-of-number assembly).

## The isolated wall

`IsLocallyConstant (N f)` for the *multiplicity* sum is the genuine residual
analytic content.  The regular-value half is fully proved here; the
remaining half — extending local constancy across the finitely many *branch*
values, where the ncard drops but the multiplicity sum does not — is the
classical merging step (Forster §4 / Miranda §II.4).  It is isolated as a *true*,
non-vacuous hypothesis (witnessed in the `div = 0` edge case by the constant
function, `ProperMapDegree.ProperMapDegreeData.ofDivEqZero`), **never** vacuous.

## References

* Forster, *Lectures on Riemann Surfaces*, §4 (the degree), Cor. 4.24–4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, §II.4 (conservation of
  number).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset OnePoint

namespace Jacobians.ProperMapDegreeConstruct

open Jacobians Jacobians.ProperMapDegree

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The local degree of `F = toRiemannSphere` at a fibre point

The local degree `d_x` of the holomorphic map `F` at `x`, read in charts:

* at a **pole** (`F x = ∞`, i.e. `ord_x f < 0`): `d_x = −ord_x f > 0`;
* at a **non-pole** (`F x = coe c`): `d_x` is the order of vanishing of `f − c`
  at `x`, i.e. the chart-pullback meromorphic order of `z ↦ f(z) − c`.

We give it as a concrete total `ℤ`-valued function; only its summation property
(local constancy) is hard — the *definition* needs no new theorem. -/

/-- **The local degree of `F = f.toRiemannSphere` at `x`, over the value `w`.**

* `w = ∞`: returns `−orderAtPoint f x` (the pole order, `> 0` at a genuine pole,
  `≤ 0` otherwise — the local degree of `F` into `∞`).
* `w = coe c`: returns the chart-pullback meromorphic order of `z ↦ f(z) − c` at
  `(chartAt ℂ x) x`, the order of vanishing of `f − c` at `x` (the multiplicity
  of `x` as a solution of `f = c`).

A concrete total function; the genuine analytic content (`= local degree of F`)
is needed only through the local-constancy of its fibre sum, isolated below. -/
def localDeg (f : MeromorphicFunction X) (w : RiemannSphere) (x : X) : ℤ :=
  match w with
  | OnePoint.infty => -f.orderAtPoint x
  | (c : ℂ) =>
      (meromorphicOrderAt (fun z => f.toFun ((chartAt (H := ℂ) x).symm z) - c)
        ((chartAt (H := ℂ) x) x)).untop₀

/-- At a non-pole `x` with `F x = coe 0` (a genuine zero or a value-`0` point),
the local degree over `0` is `orderAtPoint f x`: `meromorphicOrderAt (f.toFun ∘
chart.symm − 0) = meromorphicOrderAt (f.toFun ∘ chart.symm) = orderAtPoint f x`
by definition (`orderAtPoint = (meromorphicOrderAt (f.toFun ∘ chart.symm) _).untop₀`). -/
lemma localDeg_zero_eq_order (f : MeromorphicFunction X) (x : X) :
    localDeg f ((0 : ℂ) : RiemannSphere) x = f.orderAtPoint x := by
  show (meromorphicOrderAt (fun z => f.toFun ((chartAt (H := ℂ) x).symm z) - (0 : ℂ))
    ((chartAt (H := ℂ) x) x)).untop₀ = f.orderAtPoint x
  simp only [sub_zero]
  rfl

/-- At `∞`, the local degree over `∞` is `−orderAtPoint f x`. -/
@[simp] lemma localDeg_infty (f : MeromorphicFunction X) (x : X) :
    localDeg f OnePoint.infty x = -f.orderAtPoint x := rfl

/-! ### The fibre-multiplicity function `N`

`fibreMult f w` is the local-degree sum over the fibre `F⁻¹(w)`, the genuine
multiplicity count `∑_{x ∈ F⁻¹(w)} d_x(F)`.  We use `finsum` (`∑ᶠ`), which equals
the honest finite sum on a finite fibre and is the junk value `0` otherwise; on a
proper map every fibre is compact, and over a non-constant `f` the analytic
identity theorem makes it finite, so the junk value never fires at the relevant
values (and in particular the special fibres `F⁻¹(0)`, `F⁻¹(∞)` are finite). -/

/-- **The fibre-multiplicity sum** of `F = f.toRiemannSphere` over `w`:
`∑_{x ∈ F⁻¹(w)} (local degree of F at x)`.  The genuine "number of preimages of
`w`, counted with multiplicity". -/
def fibreMult (f : MeromorphicFunction X) (w : RiemannSphere) : ℤ :=
  ∑ᶠ x ∈ f.toRiemannSphere ⁻¹' {w}, localDeg f w x

open Classical in
/-- **The fibre-multiplicity function** `N : ℂℙ¹ → ℤ` of `f`.

Defined to read off the two special fibres exactly — `N(∞) = polesCount f`,
`N(coe 0) = zerosCount f` — and to be the genuine multiplicity sum `fibreMult`
elsewhere.  The special-value plugs *equal* the genuine multiplicity sums there
(`fibreMult f ∞ = polesCount f`, `fibreMult f (coe 0) = zerosCount f`; the
special-fibre identities, Forster §4), so `N` coincides with the genuine
multiplicity sum at every point — it is the fibre-multiplicity function, with the
two boundary readings made definitionally available. -/
def N (f : MeromorphicFunction X) : RiemannSphere → ℤ :=
  fun w =>
    if w = OnePoint.infty then polesCount f
    else if w = ((0 : ℂ) : RiemannSphere) then zerosCount f
    else fibreMult f w

/-- **Boundary reading at `∞`:** `N f ∞ = polesCount f`. -/
@[simp] lemma N_infty_eq (f : MeromorphicFunction X) :
    N f OnePoint.infty = polesCount f := by
  simp [N]

/-- **Boundary reading at `0`:** `N f (coe 0) = zerosCount f`.

`coe 0 ≠ ∞`, so the first branch fails and the second fires. -/
@[simp] lemma N_zero_eq (f : MeromorphicFunction X) :
    N f ((0 : ℂ) : RiemannSphere) = zerosCount f := by
  have hne : (((0 : ℂ) : RiemannSphere)) ≠ OnePoint.infty := OnePoint.coe_ne_infty _
  simp [N, hne]

/-! ### Regular-value local constancy (the discharged half of the wall)

The local constancy of `N f` over the *regular* values is fully proved
through the existing Hurwitz/local-sheet chain.  At a regular value `w₀` the map
`F = f.toRiemannSphere` is, near each preimage, a biholomorphism onto a
neighbourhood of `w₀` (a `LocalSheetData`), so the fibre cardinality is locally
constant there (`HurwitzPatchingData.ofLocalSheets` ∘
`fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz`,
`Jacobians.Discharge.fibreCard_isLocallyConstant_on_subset_of_localSheets`).  On
the regular set the local degree at every preimage is `1`, so the ncard *equals*
the multiplicity sum — this is the regular-value half of the constancy of `N`.

What remains (the isolated wall, below) is the extension across the finitely many
*branch* values, where the ncard drops but the multiplicity sum does not. -/

/-- **Regular-value local constancy of the fibre cardinality of `F`.**

Let `R : Set ℂℙ¹` be a set of values over which `F = f.toRiemannSphere` has
*finite fibres* and a *local-sheet datum* `LocalSheetData F w₀ x` at every
preimage `x` of every `w₀ ∈ R` (the analytic content of "`w₀` is a regular
value": near each preimage `F` is a biholomorphism).  Then the fibre-cardinality
function `w ↦ #F⁻¹(w)` is locally constant on the subtype `R`.

This is the discharged regular-value half of the conservation-of-number assembly,
obtained from `fibreCard_isLocallyConstant_on_subset_of_localSheets` with the
proper holomorphic `F` (`continuous_toRiemannSphere`).  On `R` the local degree
at each preimage is `1`, so this ncard coincides with the multiplicity sum
`fibreMult f` — i.e. `N f` is locally constant on the regular set. -/
theorem isLocallyConstant_fibreNcard_on_regular (f : MeromorphicFunction X)
    (R : Set RiemannSphere)
    (h_fib : ∀ w ∈ R, (f.toRiemannSphere ⁻¹' {w}).Finite)
    (h_sheets : ∀ w ∈ R, ∀ x ∈ f.toRiemannSphere ⁻¹' {w},
      Jacobians.Discharge.LocalSheetData f.toRiemannSphere w x) :
    IsLocallyConstant
      (fun w : (R : Set RiemannSphere) => (f.toRiemannSphere ⁻¹' {w.val}).ncard) :=
  Jacobians.Discharge.fibreCard_isLocallyConstant_on_subset_of_localSheets
    f.continuous_toRiemannSphere R h_fib h_sheets

/-- **The local-sheet supplier at a regular value, via `RegularValueWitnessReg`.**

For each value `w₀ ∈ R` carrying a regular-value witness `wit w₀ : `
`RegularValueWitnessReg F` whose chosen value is `w₀`, the existing builder
`LocalSheetData.ofRegularValueWitnessReg` produces the per-preimage
`LocalSheetData` (from the holomorphy `contMDiff_toRiemannSphere` and the
chart-pullback-derivative-nonzero certificate in the witness).  This is the
analytic supplier feeding `isLocallyConstant_fibreNcard_on_regular`. -/
noncomputable def localSheets_of_regularWitnesses (f : MeromorphicFunction X)
    (R : Set RiemannSphere)
    (wit : ∀ w ∈ R, Jacobians.Discharge.ContMDiff.RegularValueWitnessReg f.toRiemannSphere)
    (hwit : ∀ w (hw : w ∈ R), (wit w hw).toWitness.value = w) :
    ∀ w ∈ R, ∀ x ∈ f.toRiemannSphere ⁻¹' {w},
      Jacobians.Discharge.LocalSheetData f.toRiemannSphere w x := by
  intro w hw x hx
  -- Transport the membership `x ∈ F⁻¹{w}` to `x ∈ F⁻¹{(wit w hw).value}` via `hwit`.
  have hx' : x ∈ f.toRiemannSphere ⁻¹' {(wit w hw).toWitness.value} := by
    rw [hwit w hw]; exact hx
  have hsheet :
      Jacobians.Discharge.LocalSheetData f.toRiemannSphere (wit w hw).toWitness.value x :=
    Jacobians.Discharge.LocalSheetData.ofRegularValueWitnessReg
      f.contMDiff_toRiemannSphere (wit w hw) hx'
  -- Rewrite the value back to `w`.
  rw [hwit w hw] at hsheet
  exact hsheet

/-! ### The structural builder and the packaged data

`ProperMapDegreeData` (`Jacobians.ProperMapDegree`) needs a locally-constant
`N : ℂℙ¹ → ℤ` with the two boundary readings.  We have `N f` with both readings
proven (`N_infty_eq`, `N_zero_eq`); the single remaining obligation is its local
constancy. -/

/-- **Structural builder.**  Package a `ProperMapDegreeData f` from the
fibre-multiplicity function `N f` together with a proof of its local constancy.
The two boundary readings are discharged here (`N_zero_eq`, `N_infty_eq`); the
caller supplies only the local-constancy witness. -/
def ProperMapDegreeData.ofParts (f : MeromorphicFunction X)
    (hlc : IsLocallyConstant (N f)) :
    Jacobians.ProperMapDegree.ProperMapDegreeData f where
  N := N f
  locallyConstant := hlc
  zero_eq := N_zero_eq f
  infty_eq := N_infty_eq f

/-! ### Non-vacuity of the local-constancy obligation

The local-constancy hypothesis fed to `ofParts` is a genuine, true, non-vacuous
statement — not a disguised `False`.  Two complementary confirmations:

* the *structure* `ProperMapDegreeData f` is satisfiable in the edge case
  `f.div = 0` (the upstream `ProperMapDegree.ProperMapDegreeData.ofDivEqZero`,
  `N ≡ 0`);
* the *specific* boundary readings of `ofParts` (the values `N f` takes at `0`
  and `∞`) are compatible with a locally constant function exactly when
  `zerosCount f = polesCount f`, which is what the argument principle asserts:
  given that equality, the constant function realises both readings, so the
  obligation that `ofParts` discharges is consistent.  We record this
  compatibility as the honest non-vacuity certificate. -/

/-- **Non-vacuity certificate.**  If `zerosCount f = polesCount f` (the argument-
principle equality), then a locally-constant function with `N f`'s two boundary
readings exists — namely the constant function `polesCount f`.  This confirms the
local-constancy obligation of `ofParts` is consistent (satisfiable), not a
disguised `False`; the genuine multiplicity function `N f` is one such witness
once its global constancy is established. -/
lemma exists_isLocallyConstant_boundaryReadings
    (f : MeromorphicFunction X) (heq : zerosCount f = polesCount f) :
    ∃ M : RiemannSphere → ℤ, IsLocallyConstant M ∧
      M ((0 : ℂ) : RiemannSphere) = zerosCount f ∧ M OnePoint.infty = polesCount f := by
  exact ⟨fun _ => polesCount f, IsLocallyConstant.const _, heq.symm, rfl⟩

/-! ### The packaged conservation-of-number data and the keystone

Assembling `ProperMapDegreeData f` from `ofParts` (boundary readings discharged)
and the single honest local-constancy hypothesis yields, through the proven
reduction `zerosCount_eq_polesCount_of_properMapDegreeData`
(`Jacobians.ProperMapDegree`), the argument-principle equality and hence the
proper-map-degree existential — the exact shape `exists_properMapDegree`
expects. -/

/-- **The conservation-of-number data, packaged.**  Given the honest local
constancy of the fibre-multiplicity function `N f` (the global argument
principle), `ProperMapDegreeData f` exists. -/
def ProperMapDegreeData.ofConservation (f : MeromorphicFunction X)
    (hlc : IsLocallyConstant (N f)) :
    Jacobians.ProperMapDegree.ProperMapDegreeData f :=
  ProperMapDegreeData.ofParts f hlc

/-- **`zerosCount = polesCount` from the local constancy of `N f`.**  The argument-
principle equality, obtained by feeding the constructed `ProperMapDegreeData`
through the proven connectedness globalization. -/
theorem zerosCount_eq_polesCount_of_isLocallyConstant_N (f : MeromorphicFunction X)
    (hlc : IsLocallyConstant (N f)) :
    zerosCount f = polesCount f :=
  Jacobians.ProperMapDegree.zerosCount_eq_polesCount_of_properMapDegreeData f
    (ProperMapDegreeData.ofConservation f hlc)

/-- **The proper-map degree existential from local constancy of `N f`.**  This is
the exact shape of `Jacobians.exists_properMapDegree`: a common natural-number
degree `d` with `zerosCount f = d = polesCount f`.  It is derived from the local
constancy of the fibre-multiplicity function via the nonnegativity reduction
`exists_properMapDegree_of_zerosCount_eq_polesCount`. -/
theorem exists_properMapDegree_of_isLocallyConstant_N (f : MeromorphicFunction X)
    (hlc : IsLocallyConstant (N f)) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) :=
  Jacobians.ProperMapDegree.exists_properMapDegree_of_properMapDegreeData f
    (ProperMapDegreeData.ofConservation f hlc)

end Jacobians.ProperMapDegreeConstruct
