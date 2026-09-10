/-
  Dolbeault ladder — the homological/combinatorial half of the skyscraper long exact sequence
  (`CohomologicalRR.exists_skyscraperLES`), i.e. the snake lemma supplying the connecting map and the
  exactness/surjectivity at `H¹` (Forster §16).

  ## What this file is

  The skyscraper SES `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` is, at the Čech-cochain level, a **short exact
  sequence of two-step cochain complexes built from nested subcomplexes of ONE ambient complex** — the
  same Čech differential `δ` acts on all three, and the three subcomplexes are nested submodules
  `C^•(𝒪_D) ≤ C^•(𝒪_{D+P}) ≤ C^•` with the quotient `Q^• := C^•(𝒪_{D+P})/C^•(𝒪_D)`. The genuinely
  homological content — the connecting map and the long-exact-sequence at `H⁰`/`H¹` — is therefore a
  pure linear-algebra **snake lemma** for that configuration, with NO analytic input.

  We build it abstractly and completely as `TwoStepSES` (the ambient/nested-subcomplex datum) together
  with:
    * `connecting : H0Q → H1A` — the connecting homomorphism, built *canonically* (no choice-of-lift
      well-definedness chase): `δ|_{D0}` corestricted through `α₁⁻¹` to `Z¹(A)`, descended along the
      isomorphism `D0/A0 ≅ ker(dQ0)` where `D0 := {b ∈ B0 : δb ∈ A1}`;
    * `exact_h0B_connecting` — exactness `range (β⁰ : H⁰(B)→H⁰(Q)) = ker connecting`;
    * `exact_connecting_h1A` — exactness `range connecting = ker (α₁* : H¹(A)→H¹(B))`;
    * `surjective_h1Map_of_h1Q` — `α₁* : H¹(A) ↠ H¹(B)` is surjective once `H¹(Q) = 0`.

  ## Wiring to `exists_skyscraperLES` (the remaining GEOMETRIC input)

  Instantiating `TwoStepSES` with the Čech subcomplexes `sections•(𝒪_D) ≤ sections•(𝒪_{D+P})` makes
  `H0A/H1A/H0B/H1B` definitionally `globalSections`/`cechH1` (Forster's `H⁰`/`H¹`), and `α₁*` the
  inclusion-induced `h1Map`. To produce the four `SkyscraperLES` fields `f₃`/`exact₂`/`exact₃`/`surj₄`
  one transports `connecting` and the two exactness statements across the **local-realization
  isomorphism** `H⁰(Q) ≅ ℂ_P = ℂ` (the order-`(−D(P)−1)` principal-part coefficient) and uses
  `H¹(Q) = 0`. BOTH of those identifications need the *local surjectivity* of the principal-part
  coefficient — i.e. the **witness sections** `(chart − chart P)^k ∈ 𝒪_{D+P}` on the cover-sets and
  overlaps meeting `P` (`LocalRealization.coeffGermLin_surjective`, valid on a chart-disk where `D` is
  supported only at `P`, `SkyscraperArrow.witnessFn_mem_OmegaD_add_single`). That is a *geometric*
  hypothesis on the cover, NOT supplied by `IsLeray` alone; it is captured honestly as an explicit
  hypothesis in `LocalRealizationData` below, from which `exists_skyscraperLES` follows by feeding
  `TwoStepSES.snake` data through the equivalences.

  Everything in this file is complete; the snake lemma is axiom-clean linear algebra.
-/
import KirovDolbeault.Dolbeault.SkyscraperArrow

open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

/-! ## The abstract snake lemma for nested two-step subcomplexes

`TwoStepSES` packages one ambient two-step cochain complex `C0 →[d0] C1 →[d1] C2` (`d1 ∘ d0 = 0`) with
two **nested** subcomplexes `A ≤ B` (`A i ≤ B i`, both preserved by `d`). The quotient subcomplex is
`Q i := B i ⧸ A i` (term-wise), and we extract the snake-lemma connecting map and exactness at the
`H⁰`/`H¹` junctions of the long exact sequence of `0 → A → B → Q → 0`. -/

/-- One ambient two-step complex `C0 →[d0] C1 →[d1] C2` (with `d1 ∘ d0 = 0`) together with two nested
`d`-stable subcomplexes `A ≤ B`. This is exactly the shape of the Čech skyscraper SES (one Čech
differential `δ`, nested `𝒪_D`-section subcomplexes). -/
structure TwoStepSES (R : Type*) [Ring R] where
  /-- Degree-0 ambient cochains. -/
  C0 : Type*
  /-- Degree-1 ambient cochains. -/
  C1 : Type*
  /-- Degree-2 ambient cochains. -/
  C2 : Type*
  [ig0 : AddCommGroup C0] [im0 : Module R C0]
  [ig1 : AddCommGroup C1] [im1 : Module R C1]
  [ig2 : AddCommGroup C2] [im2 : Module R C2]
  /-- Ambient differential `δ⁰`. -/
  d0 : C0 →ₗ[R] C1
  /-- Ambient differential `δ¹`. -/
  d1 : C1 →ₗ[R] C2
  /-- `δ¹ ∘ δ⁰ = 0`. -/
  hd : d1 ∘ₗ d0 = 0
  /-- The smaller subcomplex `A` (e.g. `𝒪_D`-sections), degreewise. -/
  A0 : Submodule R C0
  A1 : Submodule R C1
  A2 : Submodule R C2
  /-- The larger subcomplex `B` (e.g. `𝒪_{D+P}`-sections), degreewise. -/
  B0 : Submodule R C0
  B1 : Submodule R C1
  B2 : Submodule R C2
  /-- `A` is contained in `B` degreewise. -/
  hAB0 : A0 ≤ B0
  hAB1 : A1 ≤ B1
  hAB2 : A2 ≤ B2
  /-- `δ⁰` preserves the `A`-subcomplex. -/
  hdA0 : A0.map d0 ≤ A1
  /-- `δ¹` preserves the `A`-subcomplex. -/
  hdA1 : A1.map d1 ≤ A2
  /-- `δ⁰` preserves the `B`-subcomplex. -/
  hdB0 : B0.map d0 ≤ B1
  /-- `δ¹` preserves the `B`-subcomplex. -/
  hdB1 : B1.map d1 ≤ B2

attribute [instance] TwoStepSES.ig0 TwoStepSES.im0 TwoStepSES.ig1 TwoStepSES.im1
  TwoStepSES.ig2 TwoStepSES.im2

/-- Membership in `p.submoduleOf q` unfolds to membership of the underlying element in `p`. (Mathlib
has `submoduleOf := comap q.subtype p` but no membership simp-lemma; this is it.) -/
@[simp] theorem mem_submoduleOf {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} {x : q} : x ∈ p.submoduleOf q ↔ (x : M) ∈ p := Iff.rfl

namespace TwoStepSES

variable {R : Type*} [Ring R] (S : TwoStepSES R)

/-- `H⁰` of a subcomplex with degree-0 part `S0`: the matching global sections `ker δ⁰ ∩ S0`. -/
def H0sub (S0 : Submodule R S.C0) : Submodule R S.C0 := LinearMap.ker S.d0 ⊓ S0

/-- `Z¹` of a subcomplex with degree-1 part `S1`: the `1`-cocycles `ker δ¹ ∩ S1`. -/
def Z1sub (S1 : Submodule R S.C1) : Submodule R S.C1 := LinearMap.ker S.d1 ⊓ S1

/-- `B¹` of a subcomplex with degree-0 part `S0`: the `1`-coboundaries `δ⁰(S0)`. -/
def B1sub (S0 : Submodule R S.C0) : Submodule R S.C1 := S0.map S.d0

/-- `H¹` of the `A`-subcomplex: `Z¹(A) ⧸ B¹(A)`. Matches the Čech `cechH1`. -/
abbrev H1A : Type _ :=
  (S.Z1sub S.A1) ⧸ (S.B1sub S.A0).submoduleOf (S.Z1sub S.A1)

/-- `H¹` of the `B`-subcomplex. -/
abbrev H1B : Type _ :=
  (S.Z1sub S.B1) ⧸ (S.B1sub S.B0).submoduleOf (S.Z1sub S.B1)

/-! ### The quotient subcomplex `Q• = B•/A•` (degrees 0,1) and its differential -/

/-- Degree-0 part of the quotient complex `Q0 = B0 ⧸ A0`. -/
abbrev Q0 : Type _ := S.B0 ⧸ S.A0.submoduleOf S.B0

/-- Degree-1 part of the quotient complex `Q1 = B1 ⧸ A1`. -/
abbrev Q1 : Type _ := S.B1 ⧸ S.A1.submoduleOf S.B1

/-- `δ⁰` corestricted to the `B`-subcomplex, `↥B0 →ₗ ↥B1`. -/
noncomputable def dB0 : S.B0 →ₗ[R] S.B1 :=
  (S.d0.domRestrict S.B0).codRestrict S.B1 fun b => S.hdB0 ⟨b.1, b.2, rfl⟩

@[simp] theorem dB0_coe (b : S.B0) : (S.dB0 b : S.C1) = S.d0 b := rfl

/-- The induced differential on the quotient complex, `dQ0 : Q0 →ₗ Q1` (`Submodule.mapQ` of `dB0`:
`δ⁰` maps `A0` into `A1`, so it descends to the quotients). -/
noncomputable def dQ0 : S.Q0 →ₗ[R] S.Q1 :=
  Submodule.mapQ _ _ S.dB0 fun b hb => by
    -- `b ∈ A0.submoduleOf B0 → dB0 b ∈ A1.submoduleOf B1`
    rw [mem_submoduleOf] at hb
    rw [Submodule.mem_comap, mem_submoduleOf]
    exact S.hdA0 ⟨b.1, hb, rfl⟩

@[simp] theorem dQ0_mk (b : S.B0) :
    S.dQ0 (Submodule.Quotient.mk b) = Submodule.Quotient.mk (S.dB0 b) := rfl

/-- `H⁰` of the quotient complex `Q`: `ker dQ0` (a submodule of `Q0`). The snake-lemma middle term. -/
noncomputable def H0Q : Submodule R S.Q0 := LinearMap.ker S.dQ0

/-! ### The "liftable" submodule `D0 ⊆ B0` and the canonical connecting datum

`D0 := {b ∈ B0 : δ⁰ b ∈ A1}` is the set of `B`-cochains whose differential lands in `A`. On it, `δ⁰`
corestricts to a map into `Z¹(A)` (it is automatically a cocycle, `δ¹δ⁰ = 0`); descending to `H¹(A)`
gives a map `ψ̄ : D0 → H¹(A)` that kills `A0`. And the quotient projection `mkQ : B0 → Q0` restricts to
a *surjection* `D0 ↠ ker dQ0` with kernel `A0`. The connecting map is `ψ̄` descended along that iso. -/

/-- `D0 = {b ∈ B0 : δ⁰ b ∈ A1}`, the elements of `B0` whose differential lies in the `A`-subcomplex.
Pulled back along `dB0` from `A1.submoduleOf B1`. -/
noncomputable def D0 : Submodule R S.B0 := S.A1.submoduleOf S.B1 |>.comap S.dB0

@[simp] theorem mem_D0 {b : S.B0} : b ∈ S.D0 ↔ (S.d0 b.1 : S.C1) ∈ S.A1 := by
  simp only [D0, Submodule.mem_comap, mem_submoduleOf, dB0_coe]

/-- `A0 ⊆ D0` (as submodules of `B0`): on `A0`, `δ⁰` already lands in `A1` (`hdA0`). -/
theorem A0_submoduleOf_le_D0 : S.A0.submoduleOf S.B0 ≤ S.D0 := by
  intro b hb
  rw [mem_submoduleOf] at hb
  rw [mem_D0]
  exact S.hdA0 ⟨b.1, hb, rfl⟩

/-- The corestriction of `δ⁰|_{D0}` to `Z¹(A)`: for `b ∈ D0`, `δ⁰ b ∈ A1` (by definition) and
`δ¹(δ⁰ b) = 0` (`hd`), so `δ⁰ b ∈ Z¹(A) = ker δ¹ ⊓ A1`. -/
noncomputable def psi : S.D0 →ₗ[R] S.Z1sub S.A1 :=
  ((S.d0.domRestrict S.B0).domRestrict S.D0).codRestrict (S.Z1sub S.A1) fun b => by
    refine ⟨?_, (mem_D0 S).mp b.2⟩
    have : S.d1 (S.d0 b.1.1) = 0 := by rw [← LinearMap.comp_apply, S.hd, LinearMap.zero_apply]
    exact this

@[simp] theorem psi_coe (b : S.D0) : (S.psi b : S.C1) = S.d0 b.1.1 := rfl

/-- `ψ` descended to `H¹(A)`: `ψ̄ : D0 →ₗ H¹(A)`, the connecting datum before quotienting the source. -/
noncomputable def psiBar : S.D0 →ₗ[R] S.H1A := (Submodule.mkQ _).comp S.psi

@[simp] theorem psiBar_apply (b : S.D0) :
    S.psiBar b = Submodule.Quotient.mk (S.psi b) := rfl

/-- `ψ̄` kills `A0`: for `a ∈ A0`, `ψ a = δ⁰ a ∈ B¹(A) = δ⁰(A0)`, hence `0` in `H¹(A)`. -/
theorem A0_submoduleOf_le_ker_psiBar :
    (S.A0.submoduleOf S.B0).submoduleOf S.D0 ≤ LinearMap.ker S.psiBar := by
  rintro ⟨b, hbD⟩ hb
  rw [mem_submoduleOf, mem_submoduleOf] at hb
  rw [LinearMap.mem_ker, psiBar_apply, Submodule.Quotient.mk_eq_zero, mem_submoduleOf, psi_coe]
  exact ⟨b.1, hb, rfl⟩

/-! ### The iso `D0 / A0 ≅ ker dQ0` and the connecting map -/

/-- The quotient projection `mkQ : B0 → Q0`, restricted to `D0` and corestricted to `ker dQ0`: for
`b ∈ D0`, `dQ0 (mk b) = mk (δ⁰ b) = 0` since `δ⁰ b ∈ A1`. -/
noncomputable def theta : S.D0 →ₗ[R] S.H0Q :=
  (((S.A0.submoduleOf S.B0).mkQ).domRestrict S.D0).codRestrict S.H0Q fun b => by
    show S.dQ0 (Submodule.Quotient.mk (b.1 : S.B0)) ∈ (⊥ : Submodule R S.Q1)
    rw [dQ0_mk, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, mem_submoduleOf]
    exact (mem_D0 S).mp b.2

@[simp] theorem theta_coe (b : S.D0) :
    (S.theta b : S.Q0) = Submodule.Quotient.mk (b.1 : S.B0) := rfl

/-- `θ` is surjective onto `ker dQ0`: an element of `ker dQ0` is `mk b` for some `b ∈ B0` with
`mk (δ⁰ b) = 0`, i.e. `δ⁰ b ∈ A1`, i.e. `b ∈ D0`. -/
theorem theta_surjective : Function.Surjective S.theta := by
  rintro ⟨q, hq⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  -- `q = mk b`, `hq : dQ0 (mk b) = 0`, i.e. `δ⁰ b ∈ A1`, so `b ∈ D0`.
  rw [H0Q, LinearMap.mem_ker, dQ0_mk, Submodule.Quotient.mk_eq_zero, mem_submoduleOf] at hq
  exact ⟨⟨b, (mem_D0 S).mpr hq⟩, Subtype.ext rfl⟩

/-- `ker θ = A0` (as a submodule of `D0`): `mk b = 0` in `Q0` iff `b ∈ A0`. -/
theorem ker_theta :
    LinearMap.ker S.theta = (S.A0.submoduleOf S.B0).submoduleOf S.D0 := by
  ext b
  rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero (p := S.H0Q), theta_coe,
    Submodule.Quotient.mk_eq_zero]
  simp only [mem_submoduleOf]

/-- **The connecting homomorphism** `δ̄ : H⁰(Q) = ker dQ0 → H¹(A)` of the snake lemma, built
*canonically*: `ψ̄ : D0 → H¹(A)` factors through `D0/ker θ ≅ ker dQ0 = H⁰(Q)` (`θ` surjective with
`ker θ = A0 ≤ ker ψ̄`). No choice-of-lift well-definedness chase. -/
noncomputable def connecting : S.H0Q →ₗ[R] S.H1A :=
  ((LinearMap.ker S.theta).liftQ S.psiBar (by
      rw [ker_theta]; exact S.A0_submoduleOf_le_ker_psiBar)) ∘ₗ
    (S.theta.quotKerEquivOfSurjective S.theta_surjective).symm.toLinearMap

/-- **The defining property of `connecting`.** On the surjection `θ : D0 ↠ H⁰(Q)`, the connecting map
is just `ψ̄` (the class of `δ⁰ b`): `connecting (θ b) = [δ⁰ b]`. The workhorse for exactness. -/
@[simp] theorem connecting_theta (b : S.D0) :
    S.connecting (S.theta b) = S.psiBar b := by
  rw [connecting, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply (f := S.theta) S.theta_surjective b,
    Submodule.liftQ_apply]

/-! ### The structural maps `H⁰(B) → H⁰(Q)` and `H¹(A) → H¹(B)` (induced by `β`, `α`)

`H⁰(B)` is taken in the `H0sub` form `ker δ⁰ ⊓ B0` (a submodule of the *ambient* `C0`) — this is the
form Forster's `globalSections` uses, so the Čech instantiation matches *definitionally*. -/

/-- A degree-0 `B`-cochain in `H⁰(B) = ker δ⁰ ⊓ B0` lies in `B0`. -/
theorem mem_B0_of_mem_H0sub {b : S.C0} (hb : b ∈ S.H0sub S.B0) : b ∈ S.B0 :=
  (Submodule.mem_inf.mp hb).2

/-- A degree-0 `B`-cochain in `H⁰(B)` is a cocycle (`δ⁰ b = 0`). -/
theorem d0_eq_zero_of_mem_H0sub {b : S.C0} (hb : b ∈ S.H0sub S.B0) : S.d0 b = 0 :=
  LinearMap.mem_ker.mp (Submodule.mem_inf.mp hb).1

/-- `β₀* : H⁰(B) = ker δ⁰ ⊓ B0 → H⁰(Q) = ker dQ0`, induced by the quotient projection `mkQ : B0 → Q0`
(it preserves cocycles: `dQ0 (mk b) = mk (δ⁰ b) = mk 0 = 0` for a global section `b`).
Built as `H⁰(B) ↪ B0 →[mkQ] Q0`, corestricted to `ker dQ0`. -/
noncomputable def h0Map : ↥(S.H0sub S.B0) →ₗ[R] S.H0Q :=
  ((S.A0.submoduleOf S.B0).mkQ.comp (Submodule.inclusion (inf_le_right : S.H0sub S.B0 ≤ S.B0))
    ).codRestrict S.H0Q fun b => by
    show S.dQ0 (Submodule.Quotient.mk (⟨b.1, b.2.2⟩ : S.B0)) ∈ (⊥ : Submodule R S.Q1)
    rw [dQ0_mk, Submodule.mem_bot,
      show S.dB0 ⟨b.1, b.2.2⟩ = 0 from
        Subtype.ext (by rw [dB0_coe]; exact S.d0_eq_zero_of_mem_H0sub b.2),
      Submodule.Quotient.mk_zero]

@[simp] theorem h0Map_coe (b : ↥(S.H0sub S.B0)) :
    (S.h0Map b : S.Q0) = Submodule.Quotient.mk (⟨b.1, S.mem_B0_of_mem_H0sub b.2⟩ : S.B0) := rfl

/-- `Z¹(A) ≤ Z¹(B)` (same `ker δ¹`, and `A1 ≤ B1`). -/
theorem Z1sub_A_le_B : S.Z1sub S.A1 ≤ S.Z1sub S.B1 :=
  inf_le_inf_left _ S.hAB1

/-- `B¹(A) ≤ B¹(B)` (`δ⁰` of `A0 ≤ B0`). -/
theorem B1sub_A_le_B : S.B1sub S.A0 ≤ S.B1sub S.B0 :=
  Submodule.map_mono S.hAB0

/-- `α₁* : H¹(A) → H¹(B)`, induced by the cocycle inclusion `Z¹(A) ↪ Z¹(B)` (it carries `A`-coboundaries
into `B`-coboundaries). In the Čech instantiation this is exactly `FiniteCover.h1Map`. -/
noncomputable def h1MapAbs : S.H1A →ₗ[R] S.H1B :=
  Submodule.mapQ _ _ (Submodule.inclusion S.Z1sub_A_le_B) (by
    rintro ⟨c, hc⟩ hcob
    rw [Submodule.mem_comap]
    rw [mem_submoduleOf] at hcob ⊢
    exact S.B1sub_A_le_B hcob)

@[simp] theorem h1MapAbs_mk (c : ↥(S.Z1sub S.A1)) :
    S.h1MapAbs (Submodule.Quotient.mk c)
      = Submodule.Quotient.mk (Submodule.inclusion S.Z1sub_A_le_B c) := rfl

/-! ### The degree-2 part of `Q` and `H¹(Q)` (for the surjectivity `surj₄`) -/

/-- Degree-2 part of the quotient complex `Q2 = B2 ⧸ A2`. -/
abbrev Q2 : Type _ := S.B2 ⧸ S.A2.submoduleOf S.B2

/-- `δ¹` corestricted to the `B`-subcomplex, `↥B1 →ₗ ↥B2`. -/
noncomputable def dB1 : S.B1 →ₗ[R] S.B2 :=
  (S.d1.domRestrict S.B1).codRestrict S.B2 fun b => S.hdB1 ⟨b.1, b.2, rfl⟩

@[simp] theorem dB1_coe (b : S.B1) : (S.dB1 b : S.C2) = S.d1 b := rfl

/-- The induced second differential `dQ1 : Q1 →ₗ Q2`. -/
noncomputable def dQ1 : S.Q1 →ₗ[R] S.Q2 :=
  Submodule.mapQ _ _ S.dB1 fun b hb => by
    rw [mem_submoduleOf] at hb
    rw [Submodule.mem_comap, mem_submoduleOf]
    exact S.hdA1 ⟨b.1, hb, rfl⟩

@[simp] theorem dQ1_mk (b : S.B1) :
    S.dQ1 (Submodule.Quotient.mk b) = Submodule.Quotient.mk (S.dB1 b) := rfl

/-- `dQ1 ∘ dQ0 = 0` (the quotient complex is a complex; inherited from `δ¹ ∘ δ⁰ = 0`). -/
theorem dQ1_comp_dQ0 : S.dQ1 ∘ₗ S.dQ0 = 0 := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [LinearMap.comp_apply, dQ0_mk, dQ1_mk, LinearMap.zero_apply]
  rw [show (S.dB1 (S.dB0 b)) = 0 from ?_, Submodule.Quotient.mk_zero]
  apply Subtype.ext
  rw [dB1_coe, dB0_coe]
  show S.d1 (S.d0 b.1) = (0 : S.C2)
  rw [← LinearMap.comp_apply, S.hd, LinearMap.zero_apply]

/-- `B¹(Q) = range dQ0` is contained in `Z¹(Q) = ker dQ1`. -/
theorem range_dQ0_le_ker_dQ1 : LinearMap.range S.dQ0 ≤ LinearMap.ker S.dQ1 := by
  rw [LinearMap.range_le_ker_iff]; exact S.dQ1_comp_dQ0

/-- `H¹(Q) = Z¹(Q)/B¹(Q) = ker dQ1 ⧸ range dQ0`. The cokernel-of-cohomology term whose vanishing
gives the surjectivity `surj₄`. -/
abbrev H1Q : Type _ :=
  ↥(LinearMap.ker S.dQ1) ⧸ (LinearMap.range S.dQ0).submoduleOf (LinearMap.ker S.dQ1)

/-! ### Exactness at `H⁰(Q)` and `H¹(A)` (the snake-lemma junctions) -/

/-- **Exactness at `H⁰(Q)`**: `range (β₀* : H⁰(B)→H⁰(Q)) = ker connecting`. A cocycle class maps to `0`
under the connecting map iff it is `β₀` of an honest `B`-global-section. -/
theorem exact_h0Map_connecting : Function.Exact S.h0Map S.connecting := by
  intro y
  constructor
  · -- `connecting y = 0 → y ∈ range h0Map`.
    intro hy
    obtain ⟨b, rfl⟩ := S.theta_surjective y
    rw [connecting_theta, psiBar_apply, Submodule.Quotient.mk_eq_zero, mem_submoduleOf,
      psi_coe] at hy
    obtain ⟨a, ha, hae⟩ := hy
    -- `δ⁰ b = δ⁰ a` with `a ∈ A0`; so `b - a ∈ H⁰(B)` and `h0Map (b - a) = θ b`.
    have haB0 : a ∈ S.B0 := S.hAB0 ha
    have hd0ba : S.d0 (b.1.1 - a) = (0 : S.C1) := by rw [map_sub, hae, sub_self]
    refine ⟨⟨b.1.1 - a, Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hd0ba,
      S.B0.sub_mem b.1.2 haB0⟩⟩, ?_⟩
    -- `h0Map (b - a) = mk (b - a) = mk b = θ b` since `(b-a) - b = -a ∈ A0`.
    apply Subtype.ext
    rw [h0Map_coe, theta_coe, Submodule.Quotient.eq, mem_submoduleOf]
    show ((b.1.1 - a) - b.1.1 : S.C0) ∈ S.A0
    rw [sub_sub_cancel_left]
    exact S.A0.neg_mem ha
  · -- `y ∈ range h0Map → connecting y = 0`.
    rintro ⟨z, rfl⟩
    -- `z ∈ H⁰(B) = ker δ⁰ ⊓ B0`, so its `B0`-lift is in `D0` and `h0Map z = θ ⟨z⟩`.
    have hzd0 : S.d0 z.1 = (0 : S.C1) := S.d0_eq_zero_of_mem_H0sub z.2
    have hzD : (⟨z.1, S.mem_B0_of_mem_H0sub z.2⟩ : S.B0) ∈ S.D0 := by
      rw [mem_D0]; show S.d0 z.1 ∈ S.A1; rw [hzd0]; exact zero_mem _
    have hθ : S.h0Map z = S.theta ⟨⟨z.1, S.mem_B0_of_mem_H0sub z.2⟩, hzD⟩ := by
      apply Subtype.ext; rw [h0Map_coe, theta_coe]
    rw [hθ, connecting_theta, psiBar_apply, Submodule.Quotient.mk_eq_zero, mem_submoduleOf, psi_coe]
    -- `δ⁰ z = 0 ∈ B¹(A)`.
    show S.d0 z.1 ∈ S.B1sub S.A0
    rw [hzd0]
    exact zero_mem _

/-- **Exactness at `H¹(A)`**: `range connecting = ker (α₁* : H¹(A)→H¹(B))`. A class in `H¹(A)` dies in
`H¹(B)` (becomes a `B`-coboundary) iff it is in the image of the connecting map. -/
theorem exact_connecting_h1Map : Function.Exact S.connecting S.h1MapAbs := by
  intro y
  constructor
  · -- `h1MapAbs y = 0 → y ∈ range connecting`.
    intro hy
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [h1MapAbs_mk, Submodule.Quotient.mk_eq_zero, mem_submoduleOf] at hy
    -- `c ∈ Z¹(A)` and `c ∈ B¹(B) = δ⁰(B0)`: `c = δ⁰ b`, `b ∈ B0`. As `c ∈ A1`, `b ∈ D0`.
    obtain ⟨b, hb, hbe⟩ := hy
    have hbD : (⟨b, hb⟩ : S.B0) ∈ S.D0 := by
      rw [mem_D0]; show S.d0 b ∈ S.A1; rw [hbe]; exact (Submodule.mem_inf.mp c.2).2
    refine ⟨S.theta ⟨⟨b, hb⟩, hbD⟩, ?_⟩
    rw [connecting_theta, psiBar_apply]
    -- `[δ⁰ b] = [c]` in `H¹(A)`, since `δ⁰ b = c` as elements of `Z¹(A)`.
    congr 1
    apply Subtype.ext
    rw [psi_coe]; exact hbe
  · -- `y ∈ range connecting → h1MapAbs y = 0`.
    rintro ⟨q, rfl⟩
    obtain ⟨b, rfl⟩ := S.theta_surjective q
    rw [connecting_theta, psiBar_apply, h1MapAbs_mk, Submodule.Quotient.mk_eq_zero, mem_submoduleOf]
    -- `[δ⁰ b]_B = 0` since `δ⁰ b ∈ B¹(B) = δ⁰(B0)` (here `b ∈ B0`).
    show (S.psi b : S.C1) ∈ S.B1sub S.B0
    rw [psi_coe]
    exact ⟨b.1.1, b.1.2, rfl⟩

/-! ### Surjectivity of `α₁* : H¹(A) → H¹(B)` from `H¹(Q) = 0` (the LES termination, `surj₄`) -/

/-- **`surj₄`: `α₁* : H¹(A) → H¹(B)` is surjective once `H¹(Q) = 0`** (here `Subsingleton H1Q`). The
last arrow of the six-term sequence `… → H¹(A) → H¹(B) → H¹(Q)`; if `H¹(Q)` is trivial the map onto
`H¹(B)` is onto. Concretely: a `B`-1-cocycle `c` maps to a `Q`-1-cocycle whose class in `H¹(Q)` is `0`,
so `c = dB0 b₀ + (A-cochain)` for some `b₀ ∈ B0`; the `A`-cochain `c − dB0 b₀` is an `A`-cocycle whose
`α₁*`-class is `[c]`. -/
theorem surjective_h1MapAbs_of_subsingleton (h : Subsingleton S.H1Q) :
    Function.Surjective S.h1MapAbs := by
  intro y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  -- `c ∈ Z¹(B) = ker δ¹ ⊓ B1`. Name the `B1`-membership, and the `B1`-lift `cB`.
  have hcZ : (c : S.C1) ∈ LinearMap.ker S.d1 := (Submodule.mem_inf.mp c.2).1
  have hcB1 : (c : S.C1) ∈ S.B1 := (Submodule.mem_inf.mp c.2).2
  set cB : S.B1 := ⟨c.1, hcB1⟩ with hcB
  -- `mk cB ∈ ker dQ1` (a `Q`-cocycle), since `dB1 cB = 0`.
  have hmkQ : (Submodule.Quotient.mk cB : S.Q1) ∈ LinearMap.ker S.dQ1 := by
    rw [LinearMap.mem_ker, dQ1_mk,
      show S.dB1 cB = 0 from Subtype.ext (by rw [dB1_coe]; exact hcZ), Submodule.Quotient.mk_zero]
  -- `[mk cB] = 0` in `H¹(Q)` (Subsingleton), so `mk cB ∈ range dQ0`.
  have hmem : (⟨_, hmkQ⟩ : ↥(LinearMap.ker S.dQ1)) ∈ (LinearMap.range S.dQ0).submoduleOf _ := by
    have : (Submodule.Quotient.mk (⟨_, hmkQ⟩ : ↥(LinearMap.ker S.dQ1)) : S.H1Q) = 0 :=
      Subsingleton.elim _ _
    rwa [Submodule.Quotient.mk_eq_zero] at this
  rw [mem_submoduleOf, LinearMap.mem_range] at hmem
  obtain ⟨qb, hqb⟩ := hmem
  obtain ⟨b₀, rfl⟩ := Submodule.Quotient.mk_surjective _ qb
  -- `dQ0 (mk b₀) = mk cB`, i.e. `mk (dB0 b₀) = mk cB`, i.e. `cB - dB0 b₀ ∈ A1`.
  rw [dQ0_mk] at hqb
  have hdiff : (cB - S.dB0 b₀ : S.B1) ∈ S.A1.submoduleOf S.B1 := by
    rw [mem_submoduleOf]
    have := (Submodule.Quotient.eq (S.A1.submoduleOf S.B1)).mp hqb.symm
    rwa [mem_submoduleOf] at this
  -- `(cB - dB0 b₀ : C1) ∈ Z¹(A)`: in `A1` (just shown) and in `ker δ¹`.
  have hcocyc : ((cB : S.C1) - (S.dB0 b₀ : S.C1)) ∈ S.Z1sub S.A1 := by
    refine Submodule.mem_inf.mpr ⟨?_, hdiff⟩
    rw [LinearMap.mem_ker, map_sub, dB0_coe]
    show S.d1 c.1 - S.d1 (S.d0 b₀.1) = (0 : S.C2)
    rw [(LinearMap.mem_ker.mp hcZ), ← LinearMap.comp_apply, S.hd, LinearMap.zero_apply, sub_zero]
  -- `α₁* [cB - dB0 b₀]_A = [c]_B`.
  refine ⟨Submodule.Quotient.mk ⟨_, hcocyc⟩, ?_⟩
  rw [h1MapAbs_mk, Submodule.Quotient.eq, mem_submoduleOf]
  -- difference `((cB - dB0 b₀) - c) = -dB0 b₀ ∈ B¹(B)`.
  show ((((cB : S.C1) - (S.dB0 b₀ : S.C1)) - (c.1 : S.C1))) ∈ S.B1sub S.B0
  rw [show (cB : S.C1) = c.1 from rfl, sub_sub_cancel_left]
  exact Submodule.neg_mem _ ⟨b₀.1, b₀.2, rfl⟩

end TwoStepSES

/-! ## Instantiation: the Čech skyscraper `TwoStepSES`

The ambient complex is the germ-class Čech complex `Cochain0 → Cochain1 → Cochain2` (one differential
`δ`), and the two nested subcomplexes are the `𝒪_D` ⊆ `𝒪_{D+P}` section subcomplexes. The homology
objects of the abstract snake are then *definitionally* Forster's Čech `H⁰`/`H¹`, and the abstract
`h1MapAbs` is the inclusion-induced `FiniteCover.h1Map`. -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

/-- 2-cochains that are `𝒪_D`-sections on each triple intersection (the degree-2 section subcomplex —
not previously needed in `CechComplex`, supplied here for the `Q`-degree-2 term of the snake). -/
def sections2 (𝔘 : FiniteCover X) (D : Divisor X) : Submodule ℂ 𝔘.Cochain2 where
  carrier := {g | ∀ t, g t ∈ OmegaDGerm D (𝔘.U t.1 ⊓ 𝔘.U t.2.1 ⊓ 𝔘.U t.2.2)}
  add_mem' hf hg t := add_mem (hf t) (hg t)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hg t := Submodule.smul_mem _ c (hg t)

/-- `δ¹` preserves the `𝒪_D` section subcomplex (each component of `δ¹g` is a signed sum of restrictions
of `𝒪_D`-germs, hence an `𝒪_D`-germ). -/
theorem cechDelta1_sections (𝔘 : FiniteCover X) (D : Divisor X) :
    Submodule.map 𝔘.cechDelta1 (𝔘.sections1 D) ≤ 𝔘.sections2 D := by
  rintro _ ⟨g, hg, rfl⟩ t
  obtain ⟨i, j, k⟩ := t
  simp only [cechDelta1, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  refine add_mem (sub_mem ?_ ?_) ?_
  · exact rawRestrictG_omegaDGerm (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (hg (j, k))
  · exact rawRestrictG_omegaDGerm (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (hg (i, k))
  · exact rawRestrictG_omegaDGerm inf_le_left (hg (i, j))

/-- **The Čech skyscraper `TwoStepSES`.** Ambient germ-class Čech complex `δ`, with the nested
subcomplexes `𝒪_D ≤ 𝒪_{D+P}` of section submodules in degrees 0,1,2. -/
noncomputable def skyscraperTwoStep (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    TwoStepSES ℂ where
  C0 := 𝔘.Cochain0
  C1 := 𝔘.Cochain1
  C2 := 𝔘.Cochain2
  d0 := 𝔘.cechDelta0
  d1 := 𝔘.cechDelta1
  hd := 𝔘.cechDelta1_comp_cechDelta0
  A0 := 𝔘.sections0 D
  A1 := 𝔘.sections1 D
  A2 := 𝔘.sections2 D
  B0 := 𝔘.sections0 (D + Finsupp.single P 1)
  B1 := 𝔘.sections1 (D + Finsupp.single P 1)
  B2 := 𝔘.sections2 (D + Finsupp.single P 1)
  hAB0 := 𝔘.sections0_le_add_single D P
  hAB1 := 𝔘.sections1_le_add_single D P
  hAB2 := fun _ hf t => OmegaDGerm_le_add_single D P _ (hf t)
  hdA0 := 𝔘.cechDelta0_sections D
  hdA1 := 𝔘.cechDelta1_sections D
  hdB0 := 𝔘.cechDelta0_sections (D + Finsupp.single P 1)
  hdB1 := 𝔘.cechDelta1_sections (D + Finsupp.single P 1)

/-! ### The remaining GEOMETRIC input, bundled honestly, and the `SkyscraperLES` assembly

`LocalRealizationData` packages exactly the facts that the *snake lemma does not* supply — the
**local-realization** isomorphism `H⁰(Q) ≅ ℂ` (with its compatibility with the principal-part arrow
`h0ToSky`) and the **acyclicity** `H¹(Q) = 0`, both of which need the local surjectivity of the
order-`(−D(P)−1)` coefficient onto `ℂ` (the witness sections `(chart − chart P)^k ∈ 𝒪_{D+P}` on
cover-sets/overlaps meeting `P`, `LocalRealization.coeffGermLin_surjective` /
`SkyscraperArrow.witnessFn_mem_OmegaD_add_single`) — a *geometric* property of the chart-disk cover,
NOT a consequence of `IsLeray` alone. Bundling them as explicit hypotheses keeps this file gap-free
while making the snake + linear-algebra reduction completely explicit.

Given `LocalRealizationData`, the four `SkyscraperLES` snake fields are immediate:
`f₃ = connecting ∘ e0.symm`, with `exact₂`/`exact₃` transported across `e0` (ladder/surjective-precomp
isomorphism transport of `exact_h0Map_connecting` / `exact_connecting_h1Map`) and `surj₄` from
`surjective_h1MapAbs_of_subsingleton`. -/

/-- The geometric input the snake lemma cannot supply, bundled honestly as explicit hypotheses (NOT a gap): the
local-realization iso `H⁰(Q) ≅ ℂ` compatible with the principal-part arrow `h0ToSky`, the acyclicity
`H¹(Q) = 0`, and the (Forster 14.9) `H¹` finiteness. -/
structure LocalRealizationData (𝔘 : FiniteCover X) (D : Divisor X) (P : X) where
  /-- A cover-set containing `P` (where the principal-part coefficient `h0ToSky` is read). -/
  i : 𝔘.ι
  /-- `P` lies in that cover-set. -/
  hP : P ∈ 𝔘.U i
  /-- **The local-realization isomorphism `H⁰(Q) ≅ ℂ`** (the order-`(−D(P)−1)` coefficient at `P`): the
  genuine 1-dimensional skyscraper stalk, in cohomology form. The analytic content of
  `LocalRealization.localRealizationGermEquiv`, lifted from the overlap to the `H⁰`-of-quotient term. -/
  e0 : (𝔘.skyscraperTwoStep D P).H0Q ≃ₗ[ℂ] ℂ
  /-- **Compatibility**: the principal-part coefficient arrow `h0ToSky` is `e0` composed with the
  cohomology projection `β₀* : H⁰(𝒪_{D+P}) → H⁰(Q)` (`h0Map`). I.e. reading the coefficient = projecting
  to `Q` and applying the realization iso. -/
  hcompat : 𝔘.h0ToSky D P hP = (e0 : (𝔘.skyscraperTwoStep D P).H0Q →ₗ[ℂ] ℂ).comp
    (𝔘.skyscraperTwoStep D P).h0Map
  /-- **Acyclicity `H¹(Q) = 0`** (the constant/skyscraper quotient complex on the star of `P` is
  acyclic in degree 1). Gives the LES termination `surj₄`. -/
  hQac : Subsingleton (𝔘.skyscraperTwoStep D P).H1Q
  /-- `H¹(𝒪_D)` is finite-dimensional (Forster 14.9). -/
  finH1D : FiniteDimensional ℂ (𝔘.cechH1 D)
  /-- `H¹(𝒪_{D+P})` is finite-dimensional (Forster 14.9). -/
  finH1DP : FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1))
  /-- `H⁰(𝒪_{D+P})` is finite-dimensional (Forster compactness via the `h0Dim_eq_lDim` bridge). -/
  finH0DP : FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P 1))

/-- The connecting homomorphism `f₃ : ℂ_P → H¹(𝒪_D)` of the skyscraper LES, from the snake-lemma
`connecting` map precomposed with the realization iso `e0.symm : ℂ ≅ H⁰(Q)`. (`Skyscraper D P = ℂ`
and `H1A = cechH1 D` are definitional.) -/
noncomputable def LocalRealizationData.f₃ {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (L : 𝔘.LocalRealizationData D P) : 𝔘.Skyscraper D P →ₗ[ℂ] 𝔘.cechH1 D :=
  (𝔘.skyscraperTwoStep D P).connecting.comp
    (L.e0.symm : ℂ →ₗ[ℂ] (𝔘.skyscraperTwoStep D P).H0Q)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Exactness at `ℂ_P`** (`exact₂`): `range h0ToSky = ker f₃`. The snake exactness
`exact_h0Map_connecting` transported across the realization iso `e0` (ladder `(id, e0, id)`). -/
theorem LocalRealizationData.exact₂ {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (L : 𝔘.LocalRealizationData D P) :
    Function.Exact (𝔘.h0ToSky D P L.hP) L.f₃ := by
  rw [L.hcompat, f₃]
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := LinearEquiv.refl ℂ ↥((𝔘.skyscraperTwoStep D P).H0sub (𝔘.skyscraperTwoStep D P).B0))
    (e₂ := L.e0)
    (e₃ := LinearEquiv.refl ℂ (𝔘.skyscraperTwoStep D P).H1A) ?_ ?_).mpr
    (𝔘.skyscraperTwoStep D P).exact_h0Map_connecting
  · ext x; simp
  · ext x
    simp only [LinearMap.comp_apply, LinearEquiv.refl_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]

set_option maxHeartbeats 1000000 in
/-- **Exactness at `H¹(𝒪_D)`** (`exact₃`): `range f₃ = ker h1Map`. The snake exactness
`exact_connecting_h1Map` precomposed by the surjective `e0.symm` (and `h1Map = h1MapAbs`). -/
theorem LocalRealizationData.exact₃ {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (L : 𝔘.LocalRealizationData D P) :
    Function.Exact L.f₃ (𝔘.h1Map D P) := by
  have h : Function.Exact ((𝔘.skyscraperTwoStep D P).connecting ∘ₗ
      (L.e0.symm : ℂ →ₗ[ℂ] (𝔘.skyscraperTwoStep D P).H0Q)) (𝔘.skyscraperTwoStep D P).h1MapAbs :=
    (L.e0.symm.surjective.comp_exact_iff_exact).mpr
      (𝔘.skyscraperTwoStep D P).exact_connecting_h1Map
  exact h

set_option maxHeartbeats 1000000 in
/-- **Surjectivity of `h1Map`** (`surj₄`): from the acyclicity `H¹(Q) = 0` via
`surjective_h1MapAbs_of_subsingleton` (and `h1Map = h1MapAbs`). -/
theorem LocalRealizationData.surj₄ {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (L : 𝔘.LocalRealizationData D P) :
    Function.Surjective (𝔘.h1Map D P) := by
  rw [show 𝔘.h1Map D P = (𝔘.skyscraperTwoStep D P).h1MapAbs from rfl]
  exact (𝔘.skyscraperTwoStep D P).surjective_h1MapAbs_of_subsingleton L.hQac

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The skyscraper long exact sequence from the snake + local realization.** Given the geometric
`LocalRealizationData`, the snake lemma produces all four remaining `SkyscraperLES` fields, completing
`exists_skyscraperLES`. The `H⁰`-arrow `h0ToSky` and `exact₁₂` come from `SkyscraperArrow`
(`exact_h0Incl_h0ToSky`); everything else (`f₃`, `exact₂`, `exact₃`, `surj₄`) is the snake transported
across `e0` and `H¹(Q) = 0`. -/
noncomputable def skyscraperLES_of_localRealization {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (L : 𝔘.LocalRealizationData D P) : SkyscraperLES 𝔘 D P :=
  haveI := L.finH1D; haveI := L.finH1DP; haveI := L.finH0DP
  { h0ToSky := 𝔘.h0ToSky D P L.hP
    exact₁₂ := 𝔘.exact_h0Incl_h0ToSky D P L.hP
    f₃ := L.f₃
    exact₂ := L.exact₂
    exact₃ := L.exact₃
    surj₄ := L.surj₄
    finH1D := L.finH1D
    finH1DP := L.finH1DP
    finH0DP := L.finH0DP }

end FiniteCover

end Jacobians.Dolbeault
