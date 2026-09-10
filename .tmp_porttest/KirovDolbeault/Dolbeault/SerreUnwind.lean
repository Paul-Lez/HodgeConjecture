/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.SerrePsiAction
import KirovDolbeault.Dolbeault.SerreResidueRealizationAssembly

/-!
# Forster §17.7 — the unwinding `ψλ = ι(w) ⟹ λ ∈ range ι_D`

This file proves the LAST `SurjectivityInputs` field (`unwind`, Forster's Lemma 17.7) against
the assembled realization `GlobalResidue.toSerreResidueRealization` (`pairing D = res ∘ cup`),
reduced to ONE isolated geometric law (`UnwindRegularity`, the §17.7 pole-bound regularity).

## The honest order arithmetic (why `w/ψ ∈ L(K−D)` is NOT free)

With `D' := D − nP`, a witness `ψλ = ι_{D'}(w)` (`ψ ∈ L(nP)`, `w ∈ L(K−D')`) suggests the
preimage `w/ψ`. But `ψ ∈ L(nP)` bounds only the POLE at `P`; ψ may carry extra zeros, so

  `ord (w/ψ) = ord w − ord ψ ≥ (D' − K) − div ψ`,   i.e.  `w/ψ ∈ L(K − E)`,
  `E := D' − div ψ ≤ D`  (since `div ψ ≥ −nP`)  —  but NOT `w/ψ ∈ L(K−D)` in general.

The upgrade `L(K−E) ∩ {ι_E-functional factors through H¹(𝒪_E) → H¹(𝒪_D)} ⊆ L(K−D)` is
exactly Forster's Lemma 17.7, proven there by evaluating `Res` on an explicit one-point
cocycle — a LOCALITY property of the residue functional that the `GlobalResidue` fields
(`res` + `nondegenerate`) do not carry and cannot prove (an adversarial `res` violates it).
Per the no-unilateral-interface-extension rule it is isolated here as the `Prop`-valued
`UnwindRegularity` (hypothesis-parametric, NO axiom, NO interface change); discharge path =
the R-lane's concrete fine-sheaf `res` (R6 simple-pole ML-tie) + an S4-style two-set
one-point cocycle. See `docs/planning/S5_BLOCKER.md` / `S5_STATEMENT.md`.

## What is PROVEN here (sorry-free, axiom-free)

* `MeromorphicFunction.Mul` + `orderW_mul` + `mul_mem_linearSystem` — the product algebra
  the division step rests on (`L(A)·L(B) ⊆ L(A+B)`, order additivity).
* `lSysInclMono` — the junk-free linear-system inclusion `L(D₁) → L(D₂)` for `D₁ ≤ D₂`.
* `cupH1_cupH1` / `cupH1_congr_germ` / `globalGerm_mul` — cup multiplicativity (the cup is
  germ multiplication, so composition of cups is the cup of the product, up to germ).
* `FiniteCover.cupH1_h1InclMono` / `h1InclMono_cupH1` / `psiMul_mk` — the cochain-identical
  compatibilities between the cup, the monotone `H¹`-inclusion, and the §17.8 `psiMul`.
* `GlobalResidue.pairing_comp_h1InclMono` — **restriction compatibility of the residue
  pairing** (`ι_E(incl u) = ι_D(u) ∘ i_{E→D}`), the formal half of 17.7.
* `GlobalResidue.unwind` — **Forster §17.7**: from `ψλ = ι_{D'}(w)` with `ψ ≠ 0`,
  `λ ∈ range ι_D` — conditional only on `UnwindRegularity`. The cancellation
  `ι_D(u) ∘ i = λ ∘ i ⟹ ι_D(u) = λ` uses the iterated-skyscraper surjectivity
  `h1InclMono_surjective` (the dual of the landed `psiMul_surjective` picture).
* The `SurjectivityInputs` assembly gate: ALL THREE fields now inhabit, from
  {`G : GlobalResidue 𝔘 K`, `hR`, `UnwindRegularity G D`} alone.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.7–17.9 (pp. 136–139).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Module

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 0 — the product of meromorphic functions and its order law

Mirrors the `Inv` layer of `SerreResidueRamifiedRealCover.lean` (charted-space footprint
only, so it applies on open submanifolds `↥U` too). -/

section MulAlgebra
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- The pointwise product of meromorphic functions is meromorphic (Mathlib
`MeromorphicAt.mul` in each chart — composition with the chart inverse commutes with the
pointwise product). -/
theorem IsMeromorphic.mul {f g : X → ℂ} (hf : IsMeromorphic X f) (hg : IsMeromorphic X g) :
    IsMeromorphic X (f * g) := fun x => by
  have h := (hf x).mul (hg x)
  have heq : (f ∘ (chartAt (H := ℂ) x).symm) * (g ∘ (chartAt (H := ℂ) x).symm)
      = (f * g) ∘ (chartAt (H := ℂ) x).symm := rfl
  rwa [heq] at h

namespace MeromorphicFunction

/-- The product `f·g` of meromorphic functions — `(f*g).toFun = f.toFun * g.toFun`. -/
noncomputable instance : Mul (MeromorphicFunction X) :=
  ⟨fun f g => ⟨f.toFun * g.toFun, f.meromorphic.mul g.meromorphic⟩⟩

@[simp] theorem mul_toFun (f g : MeromorphicFunction X) :
    (f * g).toFun = f.toFun * g.toFun := rfl

/-- **Order additivity for products**: `orderW (f·g) = orderW f + orderW g` (Mathlib
`meromorphicOrderAt_mul`, read in the chart at `x`). -/
theorem orderW_mul (f g : MeromorphicFunction X) (x : X) :
    (f * g).orderW x = f.orderW x + g.orderW x := by
  show meromorphicOrderAt ((f.toFun * g.toFun) ∘ (chartAt (H := ℂ) x).symm) _
    = meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) _
      + meromorphicOrderAt (g.toFun ∘ (chartAt (H := ℂ) x).symm) _
  have heq : (f.toFun * g.toFun) ∘ (chartAt (H := ℂ) x).symm
      = (f.toFun ∘ (chartAt (H := ℂ) x).symm) * (g.toFun ∘ (chartAt (H := ℂ) x).symm) := rfl
  rw [heq, meromorphicOrderAt_mul (f.meromorphic x) (g.meromorphic x)]

end MeromorphicFunction

end MulAlgebra

/-- **`L(A)·L(B) ⊆ L(A+B)`** — the linear-system product law (order additivity). -/
theorem MeromorphicFunction.mul_mem_linearSystem {A B : Divisor X}
    {f g : MeromorphicFunction X} (hf : f ∈ linearSystem (X := X) A)
    (hg : g ∈ linearSystem (X := X) B) :
    f * g ∈ linearSystem (X := X) (A + B) := by
  intro x
  rw [MeromorphicFunction.orderW_mul]
  have h := add_le_add (hf x) (hg x)
  have hz : -((A + B : Divisor X) x) = -(A x) + -(B x) := by
    rw [Finsupp.add_apply]; ring
  have hcoe : (-((A + B : Divisor X) x) : WithTop ℤ)
      = (-(A x) : WithTop ℤ) + (-(B x) : WithTop ℤ) := by exact_mod_cast hz
  rw [hcoe]
  exact h

/-- The linear system is monotone in the divisor (`D₁ ≤ D₂` pointwise ⟹ `L(D₁) ⊆ L(D₂)`). -/
theorem linearSystem_le_of_le {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) :
    linearSystem (X := X) D₁ ≤ linearSystem (X := X) D₂ := by
  intro f hf x
  refine le_trans ?_ (hf x)
  exact_mod_cast neg_le_neg (h x)

/-- `E ≤ D` pointwise flips to `K − D ≤ K − E` pointwise. -/
theorem divisor_sub_le_sub_left {E D : Divisor X} (K : Divisor X) (hED : ∀ x, E x ≤ D x) :
    ∀ x, (K - D : Divisor X) x ≤ (K - E : Divisor X) x := fun x => by
  rw [Finsupp.sub_apply, Finsupp.sub_apply]
  have := hED x
  omega

namespace Dolbeault

/-! ## Part 1 — the junk-free linear-system inclusion `L(D₁) → L(D₂)` (`D₁ ≤ D₂`) -/

/-- The monotone inclusion `L(D₁) → L(D₂)` on the junk-free linear-system modules
(`Submodule.inclusion` descended through the germ-zero quotients). -/
noncomputable def lSysInclMono {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x) :
    lSysModule (X := X) D₁ →ₗ[ℂ] lSysModule (X := X) D₂ := by
  refine Submodule.mapQ _ _ (Submodule.inclusion (linearSystem_le_of_le h)) ?_
  intro f hf
  rw [Submodule.submoduleOf, Submodule.mem_comap] at hf
  rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap]
  exact hf

@[simp] theorem lSysInclMono_mk {D₁ D₂ : Divisor X} (h : ∀ x, D₁ x ≤ D₂ x)
    (f : ↥(linearSystem (X := X) D₁)) :
    lSysInclMono h (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (Submodule.inclusion (linearSystem_le_of_le h) f) := rfl

/-- `lSysCongr` on a representative: transport along a divisor equality keeps the underlying
meromorphic function (memberships are proof-irrelevant). -/
theorem lSysCongr_mk {D₁ D₂ : Divisor X} (h : D₁ = D₂) (f : MeromorphicFunction X)
    (hf₁ : f ∈ linearSystem (X := X) D₁) (hf₂ : f ∈ linearSystem (X := X) D₂) :
    lSysCongr h (Submodule.Quotient.mk ⟨f, hf₁⟩) = Submodule.Quotient.mk ⟨f, hf₂⟩ := by
  subst h
  rfl

/-! ## Part 2 — cup multiplicativity (germ level) -/

/-- `globalGerm` is multiplicative: the germ of a product is the product of the germs. -/
theorem globalGerm_mul (f g : MeromorphicFunction X) (U : Opens X) :
    globalGerm (f * g) U = globalGerm f U * globalGerm g U := rfl

variable {𝔉 : FiniteFamily X}

/-- **Cup composition is the cup of the product**: `(g·) ∘ (f·) = ((g·f)·)` on `H¹`
(cochain level: `mul_assoc` of germs). -/
theorem cupH1_cupH1 {D₀ D₁ D₂ : Divisor X} {f g : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (D₁ - D₀)) (hg : g ∈ linearSystem (X := X) (D₂ - D₁))
    (hgf : g * f ∈ linearSystem (X := X) (D₂ - D₀)) (ξ : 𝔉.cechH1 D₀) :
    cupH1 (𝔘 := 𝔉) hg (cupH1 (𝔘 := 𝔉) hf ξ) = cupH1 (𝔘 := 𝔉) hgf ξ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [cupH1_mk, cupH1_mk, cupH1_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  funext p
  simp only [cupCocyclesMap_coe, cupCochain1_apply]
  rw [globalGerm_mul, mul_assoc]

/-- The cup product depends only on the germ of the multiplier. -/
theorem cupH1_congr_germ {D₀ D₁ : Divisor X} {f g : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (D₁ - D₀)) (hg : g ∈ linearSystem (X := X) (D₁ - D₀))
    (hfg : ∀ U : Opens X, globalGerm f U = globalGerm g U) (ξ : 𝔉.cechH1 D₀) :
    cupH1 (𝔘 := 𝔉) hf ξ = cupH1 (𝔘 := 𝔉) hg ξ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [cupH1_mk, cupH1_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  funext p
  simp only [cupCocyclesMap_coe, cupCochain1_apply]
  rw [hfg]

namespace FiniteCover

/-! ## Part 3 — compatibilities between the cup, the monotone `H¹`-inclusion, and `psiMul`

All three are cochain-IDENTICAL statements (the monotone inclusion is the identity on
cochains; the cup multiplies by the same global germ at every divisor level). -/

/-- **Restriction compatibility of the cup** (`E ≤ D`): cupping at level `D` after the
inclusion `H¹(𝒪_E) → H¹(𝒪_D)` equals cupping at level `E`. -/
theorem cupH1_h1InclMono (𝔘 : FiniteCover X) {E D K : Divisor X}
    (hED : ∀ x, E x ≤ D x) {f : MeromorphicFunction X}
    (hfD : f ∈ linearSystem (X := X) (K - D)) (hfE : f ∈ linearSystem (X := X) (K - E))
    (ξ : 𝔘.cechH1 E) :
    cupH1 (𝔘 := 𝔘.toFiniteFamily) hfD (𝔘.h1InclMono hED ξ)
      = cupH1 (𝔘 := 𝔘.toFiniteFamily) hfE ξ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [𝔘.h1InclMono_mk, cupH1_mk, cupH1_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- **The level-shifted cup factors the unshifted one**: composing the cup
`H¹(𝒪_{D₀}) → H¹(𝒪_E)` with the inclusion `H¹(𝒪_E) → H¹(𝒪_D)` is the cup into `H¹(𝒪_D)`. -/
theorem h1InclMono_cupH1 (𝔘 : FiniteCover X) {D₀ E D : Divisor X}
    (hED : ∀ x, E x ≤ D x) {f : MeromorphicFunction X}
    (hfE : f ∈ linearSystem (X := X) (E - D₀)) (hfD : f ∈ linearSystem (X := X) (D - D₀))
    (ξ : 𝔘.cechH1 D₀) :
    𝔘.h1InclMono hED (cupH1 (𝔘 := 𝔘.toFiniteFamily) hfE ξ)
      = cupH1 (𝔘 := 𝔘.toFiniteFamily) hfD ξ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [cupH1_mk, 𝔘.h1InclMono_mk, cupH1_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- `psiMul` on a representative is the plain cup with the transported membership. -/
theorem psiMul_mk (𝔘 : FiniteCover X) (D : Divisor X) (P : X) (n : ℕ)
    (ψs : ↥(linearSystem (X := X) (Finsupp.single P (n : ℤ))))
    (hmem : (ψs : MeromorphicFunction X)
      ∈ linearSystem (X := X) (D - (D - Finsupp.single P (n : ℤ))))
    (ξ : 𝔘.cechH1 (D - Finsupp.single P (n : ℤ))) :
    𝔘.psiMul D P n (Submodule.Quotient.mk ψs) ξ
      = cupH1 (𝔘 := 𝔘.toFiniteFamily) hmem ξ := by
  rw [psiMul_apply,
    lSysCongr_mk (sub_sub_cancel D (Finsupp.single P (n : ℤ))).symm
      (ψs : MeromorphicFunction X) ψs.2 hmem]
  rfl

end FiniteCover

/-! ## Part 4 — restriction compatibility of the residue pairing, the §17.7 law, and the
unwinding -/

namespace GlobalResidue

variable {𝔘 : FiniteCover X} {K : Divisor X}

/-- **Restriction compatibility of the residue pairing** (the formal half of Forster 17.7):
for `E ≤ D` and `u ∈ L(K−D)`, `ι_E(u) = ι_D(u) ∘ i_{E→D}` — derivable for the assembled
pairing `res ∘ cup` because the inclusion is the identity on cochains. -/
theorem pairing_comp_h1InclMono (G : GlobalResidue 𝔘 K) {E D : Divisor X}
    (hED : ∀ x, E x ≤ D x) (u : lSysModule (X := X) (K - D)) :
    G.pairing E (lSysInclMono (divisor_sub_le_sub_left K hED) u)
      = (G.pairing D u) ∘ₗ 𝔘.h1InclMono hED := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  refine LinearMap.ext fun ξ => ?_
  rw [LinearMap.comp_apply, lSysInclMono_mk, G.pairing_apply, G.pairing_apply, cup_mk, cup_mk]
  exact congrArg G.res (𝔘.cupH1_h1InclMono hED f.2 _ ξ).symm

/-- **[ISOLATED INPUT — Forster §17.7 pole-bound regularity].**  If the level-`E` residue
functional `ι_E(v)` of `v ∈ L(K−E)` factors through the monotone inclusion
`H¹(𝒪_E) → H¹(𝒪_D)` (`E ≤ D`), then `v` lies in the smaller system `L(K−D)`.

This is the geometric heart of Forster's Lemma 17.7 (GTM 81, p. 137), proven there by
evaluating `Res` on an explicit one-point two-set-cover cocycle (`z^{−1−ord v}` at a point
where the `L(K−D)` bound would fail — the product has a SIMPLE pole, so the discharge sits
exactly on the R-lane's R6 simple-pole Mittag–Leffler tie).  It is a LOCALITY property of the
residue functional that the `GlobalResidue` fields (`res` + `nondegenerate`) provably do not
determine, and it is NOT derivable by dimension count without circularity (the count
`l(K−E) − l(K−D) = h¹(E) − h¹(D)` IS Serre duality).  Kept hypothesis-parametric (no axiom,
no interface change) pending the interface decision — `docs/planning/S5_BLOCKER.md`. -/
def UnwindRegularity (G : GlobalResidue 𝔘 K) (D : Divisor X) : Prop :=
  ∀ (E : Divisor X) (hED : ∀ x, E x ≤ D x) (v : lSysModule (X := X) (K - E))
    (lam : Module.Dual ℂ (𝔘.cechH1 D)),
    G.pairing E v = lam ∘ₗ 𝔘.h1InclMono hED →
    ∃ u : lSysModule (X := X) (K - D),
      lSysInclMono (divisor_sub_le_sub_left K hED) u = v

/-- **Forster §17.7 — the unwinding** (the LAST `SurjectivityInputs` field): if
`ψλ = ι_{D−nP}(w)` with `ψ ≠ 0`, then `λ ∈ range ι_D`, conditional only on the isolated
pole-bound regularity law `UnwindRegularity`.

Proof: pick a germ-nonzero representative `ψ₀` (identity theorem); the honest division step
gives `φ := w·ψ₀⁻¹ ∈ L(K−E)` for `E := (D−nP) − div ψ₀ ≤ D` (order additivity — NOT
`L(K−D)`, since ψ may have extra zeros).  Multiplication by `ψ₀` is onto
`H¹(𝒪_{D−nP}) → H¹(𝒪_E)` (germ inverse), and through it the hypothesis transports to the
factorization `ι_E(φ) = λ ∘ i_{E→D}`.  The regularity law upgrades `φ` to `u ∈ L(K−D)`;
restriction compatibility plus surjectivity of `i_{E→D}` (iterated skyscraper,
`h1InclMono_surjective`) cancel the composition, giving `ι_D(u) = λ`. -/
theorem unwind (G : GlobalResidue 𝔘 K) (hR : 𝔘.LocallyRealizable)
    {D : Divisor X} (P : X) (hreg : G.UnwindRegularity D)
    (lam : Module.Dual ℂ (𝔘.cechH1 D)) (n : ℕ)
    (ψ : lSysModule (X := X) (Finsupp.single P (n : ℤ)))
    (w : lSysModule (X := X) (K - (D - Finsupp.single P (n : ℤ))))
    (hψ : ψ ≠ 0)
    (hmatch : 𝔘.psiAct D P lam n ψ = G.pairing (D - Finsupp.single P (n : ℤ)) w) :
    lam ∈ Set.range (G.pairing D) := by
  classical
  obtain ⟨ψs, rfl⟩ := Submodule.Quotient.mk_surjective _ ψ
  obtain ⟨ws, hws⟩ := Submodule.Quotient.mk_surjective _ w
  rw [← hws] at hmatch
  set ψ₀ : MeromorphicFunction X := (ψs : MeromorphicFunction X) with hψ₀
  set w₀ : MeromorphicFunction X := (ws : MeromorphicFunction X) with hw₀
  -- ψ is germ-nonzero EVERYWHERE (identity theorem on the connected `X`).
  have hψ0 : ∃ x, ψ₀.orderW x ≠ ⊤ := by
    by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    exact hψ ((Submodule.Quotient.mk_eq_zero _).mpr fun x => hc x)
  have hne : ∀ x, ψ₀.orderW x ≠ ⊤ := ψ₀.orderW_ne_top_of_exists hψ0
  -- The divisor of ψ obeys `div ψ ≥ −nP`.
  have hdivψ : ∀ x, -(Finsupp.single P (n : ℤ) x) ≤ MeromorphicFunction.div X ψ₀ x := by
    intro x
    have h1 := ψs.2 x
    rw [← hψ₀, ← MeromorphicFunction.coe_div_eq_orderW hne x] at h1
    exact_mod_cast h1
  -- The honest division level: `E := (D − nP) − div ψ ≤ D`.
  set E : Divisor X :=
    (D - Finsupp.single P (n : ℤ)) - MeromorphicFunction.div X ψ₀ with hE
  have hED : ∀ x, E x ≤ D x := by
    intro x
    have h1 := hdivψ x
    simp only [hE, Finsupp.sub_apply]
    omega
  -- ψ multiplies `𝒪_{D−nP}` into `𝒪_E` exactly (`ord ψ = div ψ`)...
  have hψE : ψ₀ ∈ linearSystem (X := X) (E - (D - Finsupp.single P (n : ℤ))) := by
    intro x
    rw [← MeromorphicFunction.coe_div_eq_orderW hne x]
    have h2 : -((E - (D - Finsupp.single P (n : ℤ)) : Divisor X) x)
        ≤ MeromorphicFunction.div X ψ₀ x := by
      simp only [hE, Finsupp.sub_apply]
      omega
    exact_mod_cast h2
  -- ...and `1/ψ` multiplies `𝒪_E` back into `𝒪_{D−nP}`.
  have hψinv : ψ₀⁻¹ ∈ linearSystem (X := X) ((D - Finsupp.single P (n : ℤ)) - E) := by
    intro x
    rw [MeromorphicFunction.orderW_inv, ← MeromorphicFunction.coe_div_eq_orderW hne x]
    have h2 : -(((D - Finsupp.single P (n : ℤ)) - E : Divisor X) x)
        ≤ -(MeromorphicFunction.div X ψ₀ x) := by
      simp only [hE, Finsupp.sub_apply]
      omega
    exact_mod_cast h2
  -- ψ at the level the §17.8 `psiMul` uses.
  have hψD : ψ₀ ∈ linearSystem (X := X) (D - (D - Finsupp.single P (n : ℤ))) := by
    rw [sub_sub_cancel]
    exact ψs.2
  -- The division step: `φ := w·ψ⁻¹ ∈ L(K−E)`.
  have hφE : w₀ * ψ₀⁻¹ ∈ linearSystem (X := X) (K - E) := by
    have h3 := MeromorphicFunction.mul_mem_linearSystem ws.2 hψinv
    rwa [sub_add_sub_cancel] at h3
  -- `φ·ψ ∈ L(K−(D−nP))`, with the germ of `w` (`φψ = w·ψ⁻¹ψ = w` off the zeros of ψ).
  have hφψ : w₀ * ψ₀⁻¹ * ψ₀
      ∈ linearSystem (X := X) (K - (D - Finsupp.single P (n : ℤ))) := by
    have h3 := MeromorphicFunction.mul_mem_linearSystem hφE hψE
    rwa [sub_add_sub_cancel] at h3
  have hgerm : ∀ U : Opens X, globalGerm (w₀ * ψ₀⁻¹ * ψ₀) U = globalGerm w₀ U := by
    intro U
    rw [globalGerm_mul, globalGerm_mul, mul_assoc, mul_comm (globalGerm ψ₀⁻¹ U),
      globalGerm_mul_inv hne, mul_one]
  -- The factorization `ι_E(φ) = λ ∘ i_{E→D}` (transport the hypothesis through `ψ·`).
  have hkey : G.pairing E (Submodule.Quotient.mk
        (⟨w₀ * ψ₀⁻¹, hφE⟩ : ↥(linearSystem (X := X) (K - E))))
      = lam ∘ₗ 𝔘.h1InclMono hED := by
    refine LinearMap.ext fun η => ?_
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ η
    -- `η = ψ·ξ` for `ξ := (1/ψ)·η` (the level-shift is an iso, no skyscraper needed).
    set ξ : 𝔘.cechH1 (D - Finsupp.single P (n : ℤ)) :=
      cupH1 (𝔘 := 𝔘.toFiniteFamily) hψinv (Submodule.Quotient.mk c) with hξ
    have hψξ : cupH1 (𝔘 := 𝔘.toFiniteFamily) hψE ξ = Submodule.Quotient.mk c := by
      rw [hξ, cupH1_mk, cupH1_mk]
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      funext p
      simp only [cupCocyclesMap_coe, cupCochain1_apply]
      rw [← mul_assoc, globalGerm_mul_inv hne, one_mul]
    calc (G.pairing E (Submodule.Quotient.mk
            (⟨w₀ * ψ₀⁻¹, hφE⟩ : ↥(linearSystem (X := X) (K - E)))))
          (Submodule.Quotient.mk c)
        = G.res (cupH1 (𝔘 := 𝔘.toFiniteFamily) hφE
            (cupH1 (𝔘 := 𝔘.toFiniteFamily) hψE ξ)) := by
          rw [G.pairing_apply, cup_mk, hψξ]
      _ = G.res (cupH1 (𝔘 := 𝔘.toFiniteFamily) hφψ ξ) := by
          rw [cupH1_cupH1 hψE hφE hφψ ξ]
      _ = G.res (cupH1 (𝔘 := 𝔘.toFiniteFamily) ws.2 ξ) := by
          rw [cupH1_congr_germ hφψ ws.2 hgerm ξ]
      _ = (G.pairing (D - Finsupp.single P (n : ℤ)) (Submodule.Quotient.mk ws)) ξ := by
          rw [G.pairing_apply, cup_mk]
      _ = (𝔘.psiAct D P lam n (Submodule.Quotient.mk ψs)) ξ :=
          (DFunLike.congr_fun hmatch ξ).symm
      _ = lam (𝔘.psiMul D P n (Submodule.Quotient.mk ψs) ξ) := rfl
      _ = lam (cupH1 (𝔘 := 𝔘.toFiniteFamily) hψD ξ) := by
          rw [𝔘.psiMul_mk D P n ψs hψD ξ]
      _ = lam (𝔘.h1InclMono hED (cupH1 (𝔘 := 𝔘.toFiniteFamily) hψE ξ)) := by
          rw [𝔘.h1InclMono_cupH1 hED hψE hψD ξ]
      _ = (lam ∘ₗ 𝔘.h1InclMono hED) (Submodule.Quotient.mk c) := by
          rw [hψξ]; rfl
  -- The §17.7 regularity law upgrades `φ ∈ L(K−E)` to `u ∈ L(K−D)`.
  obtain ⟨u, hu⟩ := hreg E hED _ lam hkey
  refine ⟨u, ?_⟩
  -- Cancellation: `ι_D(u) ∘ i = ι_E(φ) = λ ∘ i` with `i` surjective (iterated skyscraper).
  have hcomp := G.pairing_comp_h1InclMono hED u
  rw [hu, hkey] at hcomp
  refine LinearMap.ext fun η => ?_
  obtain ⟨ζ, rfl⟩ := 𝔘.h1InclMono_surjective hR hED η
  exact (DFunLike.congr_fun hcomp ζ).symm

end GlobalResidue

/-! ## Statement gate — `SurjectivityInputs` fully assembles

ALL THREE fields of the §17.9 skeleton (`psiAct`, `psiAct_injective`, `unwind`) are now
supplied from {`G : GlobalResidue 𝔘 K`, `hR : LocallyRealizable`, `UnwindRegularity G D`}:
the §17.9 surjectivity of the Serre residue pairing is conditional on exactly the global
residue functional (Lane R) and the isolated §17.7 regularity law. -/

example {𝔘 : FiniteCover X} {K : Divisor X} (G : GlobalResidue 𝔘 K)
    (D : Divisor X) (P : X) (hR : 𝔘.LocallyRealizable)
    (hreg : G.UnwindRegularity D) :
    SurjectivityInputs G.toSerreResidueRealization D where
  P := P
  psiAct := fun lam n => 𝔘.psiAct D P lam n
  psiAct_injective := fun lam hlam n => 𝔘.psiAct_injective hR D P lam hlam n
  unwind := fun lam _hlam n ψ w hψ0 hmatch => G.unwind hR P hreg lam n ψ w hψ0 hmatch

/-- **§17.9 surjectivity, end-to-end form**: with the skeleton's
`SurjectivityInputs.pairing_surjective`, the assembled residue pairing is SURJECTIVE at `D`
given only the global residue functional and the §17.7 regularity law at `D`. -/
theorem pairing_surjective_of_globalResidue {𝔘 : FiniteCover X} {K : Divisor X}
    (G : GlobalResidue 𝔘 K) (D : Divisor X) (P : X) (hR : 𝔘.LocallyRealizable)
    (hreg : G.UnwindRegularity D) :
    Function.Surjective (G.toSerreResidueRealization.pairing D) :=
  SurjectivityInputs.pairing_surjective
    { P := P
      psiAct := fun lam n => 𝔘.psiAct D P lam n
      psiAct_injective := fun lam hlam n => 𝔘.psiAct_injective hR D P lam hlam n
      unwind := fun lam _hlam n ψ w hψ0 hmatch => G.unwind hR P hreg lam n ψ w hψ0 hmatch }
    hR

end Dolbeault

end Jacobians

end
