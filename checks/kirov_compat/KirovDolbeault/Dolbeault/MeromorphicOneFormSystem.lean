/-
  The meromorphic-1-form linear system `Ω_D` (Forster §17.4), the 1-form analog of the
  function linear system `L(D) = H⁰(𝒪_D)`.

  This is **Gate (C)** of the Forster §17 Serre-duality tower:
  the space of global meromorphic 1-forms `α` with `div α ≥ −D` (poles bounded by `D`), built as
  a `Submodule ℂ` of a meromorphic-1-form type, with its junk-free module
  (`Ω_D ⧸ germ-zero`), `omegaDim D := finrank ℂ` of it, and the soundness anchor
  `Ω_0 ⊇ HolomorphicOneForms` (every holomorphic form is a meromorphic 1-form with no pole).

  ## Representation (mirror of `MeromorphicFunction`)

  `MeromorphicFunction` (`Jacobians.Abel`) stores a bare map `toFun : X → ℂ` plus the predicate
  `IsMeromorphic` (meromorphic in every canonical chart).  A meromorphic 1-form is the *same idea
  on the cotangent bundle*: a section `toFun : ∀ x, TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ` (the **same
  fibre** as `HolomorphicOneForms X = ContMDiffSection … (cotangent)`), whose coordinate
  coefficient `formCoeff` — read in the canonical chart exactly as `Montel.localRep` reads a
  holomorphic form — is `MeromorphicAt` at every chart-image point.  This makes:

  * the order `formOrderW` (chart-coefficient `meromorphicOrderAt`) and the system `Ω_D` mirror
    `orderW`/`linearSystem` *verbatim* (same Mathlib `meromorphicOrderAt` lemmas);
  * `Ω_0 ⊇ HolomorphicOneForms` clean — a holomorphic form's `localRep` coefficient is **analytic**
    (`Montel.localRep_analyticOn_chartTarget`), hence meromorphic with order `≥ 0`
    (`AnalyticAt.meromorphicAt`, `AnalyticAt.meromorphicOrderAt_nonneg`).

  The junk-free quotient is the campaign's recurring soundness fix: a raw section space carries
  `toFun`-germ junk (a section whose germ is `0` everywhere but is a nonzero element), so the genuine
  finite dimension `omegaDim` is the quotient by the germ-zero submodule — exactly as `lDim` quotients
  `linearSystem` by `germZeroSubmodule`.

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4 (`ω·: 𝒪_{D+K} ≅ Ω_D`); the
  `linearSystem`/`lSysModule`/`lDim` pattern in `Jacobians.LinearSystem`.
-/
import KirovDolbeault.LinearSystem
import KirovDolbeault.Dolbeault.FormCoeff

open scoped Manifold ContDiff Topology Bundle
open Module

namespace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1: the meromorphic-1-form type, mirroring `MeromorphicFunction`

A 1-form is a section of the cotangent bundle; its fibre at `x` is `TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`
(written via `Bundle.Trivial X ℂ`, exactly as in `HolomorphicOneForms`).  We read its coordinate
coefficient with the same `Montel.localRep` formula, so the analyticity/meromorphy bridges and the
`meromorphicOrderAt` order theory transfer directly. -/

/-- The cotangent fibre at `x`, the codomain of a 1-form section (matches `HolomorphicOneForms`). -/
abbrev FormFiber (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) : Type _ :=
  TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x

/-- The **coordinate coefficient** of a 1-form section `σ` in the canonical chart at `x`, read
exactly as `Montel.localRep`: `σ` applied at `(chart x).symm z` to the unit coordinate tangent
transported from the model space.  Near `x`, `σ = formCoeff σ x (z) · dz` in `z = chartAt ℂ x`.
For a *holomorphic* form this is `Montel.localRep` composed with `chart.symm` (= `FormCoeff.coeffAt`),
hence analytic. -/
noncomputable def formCoeff (σ : ∀ x, FormFiber X x) (x : X) : ℂ → ℂ :=
  fun z => σ ((chartAt ℂ x).symm z)
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ ((chartAt ℂ x).symm z) 1)

/-- A section of the cotangent bundle is a **meromorphic 1-form** if its coordinate coefficient is
`MeromorphicAt` at the chart image of every point — the 1-form analog of `IsMeromorphic`. -/
def IsMeromorphicOneForm (σ : ∀ x, FormFiber X x) : Prop :=
  ∀ x : X, MeromorphicAt (formCoeff σ x) ((chartAt ℂ x) x)

/-- The type of meromorphic 1-forms on `X` — the 1-form analog of `MeromorphicFunction`. -/
structure MeromorphicOneForm (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ where
  /-- The underlying cotangent-bundle section. -/
  toFun : ∀ x, FormFiber X x
  /-- The coordinate coefficient is meromorphic in every chart. -/
  meromorphic : IsMeromorphicOneForm toFun

namespace MeromorphicOneForm


/-- Two meromorphic 1-forms are equal iff their underlying sections agree (the meromorphy field is
a `Prop`). -/
@[ext] theorem ext {α β : MeromorphicOneForm X} (h : α.toFun = β.toFun) : α = β := by
  obtain ⟨a, ha⟩ := α; obtain ⟨b, hb⟩ := β; subst h; rfl

theorem toFun_injective :
    Function.Injective (MeromorphicOneForm.toFun : MeromorphicOneForm X → ∀ x, FormFiber X x) :=
  fun _ _ h => ext h

end MeromorphicOneForm

/-! ### Meromorphy is preserved by the pointwise vector-space operations on sections

These follow from the function-level lemmas because `formCoeff` is ℂ-linear in `σ` (the fibre maps
are continuous-linear and the trivialization frame is fixed). -/

section Algebra

/-- `formCoeff` is additive in the section. -/
theorem formCoeff_add (σ τ : ∀ x, FormFiber X x) (x : X) :
    formCoeff (σ + τ) x = formCoeff σ x + formCoeff τ x := by
  funext z; simp [formCoeff]

/-- `formCoeff` negates with the section. -/
theorem formCoeff_neg (σ : ∀ x, FormFiber X x) (x : X) :
    formCoeff (-σ) x = -formCoeff σ x := by
  funext z; simp [formCoeff]

/-- `formCoeff` is ℂ-homogeneous in the section. -/
theorem formCoeff_smul (c : ℂ) (σ : ∀ x, FormFiber X x) (x : X) :
    formCoeff (c • σ) x = c • formCoeff σ x := by
  funext z; simp [formCoeff]

theorem IsMeromorphicOneForm.add {σ τ : ∀ x, FormFiber X x}
    (hσ : IsMeromorphicOneForm σ) (hτ : IsMeromorphicOneForm τ) :
    IsMeromorphicOneForm (σ + τ) := by
  intro x; rw [formCoeff_add]; exact (hσ x).add (hτ x)

theorem IsMeromorphicOneForm.neg {σ : ∀ x, FormFiber X x} (hσ : IsMeromorphicOneForm σ) :
    IsMeromorphicOneForm (-σ) := by
  intro x; rw [formCoeff_neg]; exact (hσ x).neg

theorem IsMeromorphicOneForm.sub {σ τ : ∀ x, FormFiber X x}
    (hσ : IsMeromorphicOneForm σ) (hτ : IsMeromorphicOneForm τ) :
    IsMeromorphicOneForm (σ - τ) := by
  rw [sub_eq_add_neg]; exact hσ.add hτ.neg

theorem IsMeromorphicOneForm.const_smul (c : ℂ) {σ : ∀ x, FormFiber X x}
    (hσ : IsMeromorphicOneForm σ) : IsMeromorphicOneForm (c • σ) := by
  intro x; rw [formCoeff_smul]; exact (MeromorphicAt.const c _).smul (hσ x)

theorem IsMeromorphicOneForm.zero : IsMeromorphicOneForm (0 : ∀ x, FormFiber X x) := by
  intro x
  have : formCoeff (0 : ∀ x, FormFiber X x) x = fun _ => 0 := by funext z; simp [formCoeff]
  rw [this]; exact MeromorphicAt.const 0 _

theorem IsMeromorphicOneForm.nsmul (n : ℕ) {σ : ∀ x, FormFiber X x}
    (hσ : IsMeromorphicOneForm σ) : IsMeromorphicOneForm (n • σ) := by
  rw [← Nat.cast_smul_eq_nsmul ℂ n σ]; exact hσ.const_smul _

theorem IsMeromorphicOneForm.zsmul (n : ℤ) {σ : ∀ x, FormFiber X x}
    (hσ : IsMeromorphicOneForm σ) : IsMeromorphicOneForm (n • σ) := by
  rw [← Int.cast_smul_eq_zsmul ℂ n σ]; exact hσ.const_smul _

end Algebra

/-! ### The ℂ-vector-space structure on `MeromorphicOneForm X` (transported along `toFun`) -/

namespace MeromorphicOneForm

section Module

noncomputable instance : Zero (MeromorphicOneForm X) := ⟨⟨0, IsMeromorphicOneForm.zero⟩⟩
noncomputable instance : Add (MeromorphicOneForm X) :=
  ⟨fun α β => ⟨α.toFun + β.toFun, IsMeromorphicOneForm.add α.meromorphic β.meromorphic⟩⟩
noncomputable instance : Neg (MeromorphicOneForm X) :=
  ⟨fun α => ⟨-α.toFun, IsMeromorphicOneForm.neg α.meromorphic⟩⟩
noncomputable instance : Sub (MeromorphicOneForm X) :=
  ⟨fun α β => ⟨α.toFun - β.toFun, IsMeromorphicOneForm.sub α.meromorphic β.meromorphic⟩⟩
noncomputable instance : SMul ℕ (MeromorphicOneForm X) :=
  ⟨fun n α => ⟨n • α.toFun, IsMeromorphicOneForm.nsmul n α.meromorphic⟩⟩
noncomputable instance : SMul ℤ (MeromorphicOneForm X) :=
  ⟨fun n α => ⟨n • α.toFun, IsMeromorphicOneForm.zsmul n α.meromorphic⟩⟩
noncomputable instance : SMul ℂ (MeromorphicOneForm X) :=
  ⟨fun c α => ⟨c • α.toFun, IsMeromorphicOneForm.const_smul c α.meromorphic⟩⟩

@[simp] theorem zero_toFun : (0 : MeromorphicOneForm X).toFun = 0 := rfl
@[simp] theorem add_toFun (α β : MeromorphicOneForm X) :
    (α + β).toFun = α.toFun + β.toFun := rfl
@[simp] theorem neg_toFun (α : MeromorphicOneForm X) : (-α).toFun = -α.toFun := rfl
@[simp] theorem sub_toFun (α β : MeromorphicOneForm X) :
    (α - β).toFun = α.toFun - β.toFun := rfl
@[simp] theorem smul_toFun (c : ℂ) (α : MeromorphicOneForm X) :
    (c • α).toFun = c • α.toFun := rfl

noncomputable instance : AddCommGroup (MeromorphicOneForm X) :=
  toFun_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => by rfl) (fun _ _ => by rfl)

/-- The underlying-section homomorphism, used to transport the `Module` structure. -/
def toFunHom : MeromorphicOneForm X →+ (∀ x, FormFiber X x) where
  toFun := MeromorphicOneForm.toFun
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance : Module ℂ (MeromorphicOneForm X) :=
  toFun_injective.module ℂ toFunHom (fun _ _ => rfl)

end Module

/-! ### The order `formOrderW` of a meromorphic 1-form (mirror of `orderW`) -/

/-- The order of a meromorphic 1-form `α` at `x`, in `WithTop ℤ`: the `meromorphicOrderAt` of its
coordinate coefficient in the canonical chart.  It is `⊤` exactly when the form's coefficient
vanishes in a punctured neighbourhood (so the zero form lies in every `Ω_D`).  Chart-independent:
under a holomorphic coordinate change the coefficient is multiplied by the non-vanishing Jacobian,
which does not change `meromorphicOrderAt`.  The 1-form analog of `MeromorphicFunction.orderW`. -/
noncomputable def formOrderW (α : MeromorphicOneForm X) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (formCoeff α.toFun x) ((chartAt ℂ x) x)

theorem formOrderW_zero (x : X) : (0 : MeromorphicOneForm X).formOrderW x = ⊤ := by
  rw [formOrderW, meromorphicOrderAt_eq_top_iff]
  refine Filter.Eventually.of_forall fun _ => ?_
  show formCoeff (0 : ∀ x, FormFiber X x) x _ = 0
  simp [formCoeff]

/-- Scaling a meromorphic 1-form by a nonzero constant does not change its order. -/
theorem formOrderW_const_smul {c : ℂ} (hc : c ≠ 0) (α : MeromorphicOneForm X) (x : X) :
    (c • α).formOrderW x = α.formOrderW x := by
  have hcoeff : formCoeff (c • α).toFun x = c • formCoeff α.toFun x := by
    rw [show (c • α).toFun = c • α.toFun from rfl, formCoeff_smul]
  rw [formOrderW, formOrderW, hcoeff]
  exact meromorphicOrderAt_smul_of_ne_zero (f := formCoeff α.toFun x)
    (g := fun _ => c) analyticAt_const (by simpa using hc)

/-- The order of a sum is at least the min of the orders (mirror of `meromorphicOrderAt_add`),
using `formCoeff (α + β) = formCoeff α + formCoeff β`. -/
theorem min_formOrderW_le_add (α β : MeromorphicOneForm X) (x : X) :
    min (α.formOrderW x) (β.formOrderW x) ≤ (α + β).formOrderW x := by
  have hcoeff : formCoeff (α + β).toFun x = formCoeff α.toFun x + formCoeff β.toFun x := by
    rw [show (α + β).toFun = α.toFun + β.toFun from rfl, formCoeff_add]
  rw [formOrderW, formOrderW, formOrderW, hcoeff]
  exact meromorphicOrderAt_add (α.meromorphic x) (β.meromorphic x)

end MeromorphicOneForm

/-! ## Part 2: the meromorphic-1-form linear system `Ω_D`, its module, and `omegaDim`

These mirror `linearSystem`, `germZeroSubmodule`, and `lDim` verbatim, on `formOrderW`. -/

/-- **The meromorphic-1-form linear system `Ω_D`** (Forster's `Ω_D`): global meromorphic 1-forms
`α` with `div α ≥ −D`, phrased on the `WithTop ℤ` order `formOrderW` (so the zero form is
automatically a member).  A `Submodule ℂ` of `MeromorphicOneForm X` — the 1-form analog of
`linearSystem D`. -/
noncomputable def omegaD (D : Divisor X) : Submodule ℂ (MeromorphicOneForm X) where
  carrier := {α | ∀ x, (-(D x) : WithTop ℤ) ≤ α.formOrderW x}
  add_mem' {α β} hα hβ := fun x =>
    le_trans (le_min (hα x) (hβ x)) (MeromorphicOneForm.min_formOrderW_le_add α β x)
  zero_mem' := fun x => by rw [MeromorphicOneForm.formOrderW_zero]; exact le_top
  smul_mem' c α hα := fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · have h0 : (c • α).formOrderW x = ⊤ := by
        rw [hc, zero_smul]; exact MeromorphicOneForm.formOrderW_zero x
      rw [h0]; exact le_top
    · rw [MeromorphicOneForm.formOrderW_const_smul hc]; exact hα x

/-- **Germ-zero "junk" 1-forms.**  The section `toFun` carries removable-singularity junk: a
meromorphic 1-form whose coefficient germ is `0` everywhere can still be a nonzero element of
`MeromorphicOneForm X`, and such forms lie in EVERY `Ω_D`.  Quotienting them out makes `omegaDim`
the genuine finite dimension — exactly the `germZeroSubmodule` fix for functions. -/
noncomputable def formGermZeroSubmodule : Submodule ℂ (MeromorphicOneForm X) where
  carrier := {α | ∀ x, α.formOrderW x = ⊤}
  add_mem' {α β} hα hβ := fun x => by
    have h := MeromorphicOneForm.min_formOrderW_le_add α β x
    rw [hα x, hβ x, min_self] at h
    exact top_le_iff.mp h
  zero_mem' := fun x => MeromorphicOneForm.formOrderW_zero x
  smul_mem' c α hα := fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · rw [hc, zero_smul]; exact MeromorphicOneForm.formOrderW_zero x
    · rw [MeromorphicOneForm.formOrderW_const_smul hc]; exact hα x

/-- **`omegaDim D = dim_ℂ (Ω_D ⧸ germ-zero junk)`** (Forster's `dim H⁰(X, Ω_D)`): the genuine
dimension of the meromorphic-1-form linear system, with the `toFun`-junk quotiented out.  The
1-form analog of `lDim`. -/
noncomputable def omegaDim (D : Divisor X) : ℕ :=
  Module.finrank ℂ
    (↥(omegaD (X := X) D) ⧸ (formGermZeroSubmodule (X := X)).submoduleOf (omegaD (X := X) D))

/-- The **junk-free meromorphic-1-form module** `Ω_D` (= `H⁰(X, Ω_D)`).  By definition
`omegaDim D = finrank ℂ (omegaDModule D)`. -/
abbrev omegaDModule (D : Divisor X) : Type _ :=
  ↥(omegaD (X := X) D) ⧸ (formGermZeroSubmodule (X := X)).submoduleOf (omegaD (X := X) D)

theorem omegaDim_eq_finrank (D : Divisor X) :
    omegaDim (X := X) D = finrank ℂ (omegaDModule (X := X) D) := rfl

/-! ### Monotonicity `D ≤ D' → Ω_D ≤ Ω_{D'}` -/

/-- **Monotonicity of the linear system.**  A larger pole bound admits more forms: `D ≤ D'`
(coefficientwise) gives `Ω_D ≤ Ω_{D'}`.  (If `−D ≤ formOrderW α` and `D ≤ D'` then
`−D' ≤ −D ≤ formOrderW α`.) -/
theorem omegaD_mono {D D' : Divisor X} (h : D ≤ D') : omegaD (X := X) D ≤ omegaD (X := X) D' := by
  intro α hα x
  refine le_trans ?_ (hα x)
  exact_mod_cast neg_le_neg (h x)

/-! ## Part 2b: multiplication of a 1-form by a meromorphic function (Forster §17.4)

`f · α` (scalar-multiply the covector by the function value `f`) is the structure map of Forster
17.4 (`ω·: 𝒪_{D+K} ≅ Ω_D`).  Its coefficient is `(f ∘ chart⁻¹) · formCoeff α`, so the order is
*additive*: `formOrderW (f · α) = orderW f + formOrderW α`.  This sends `L(D) × Ω_E → Ω_{D+E}`. -/

/-- **Multiplication of a meromorphic 1-form by a meromorphic function.**  `(f · α)(x) := f(x) • α(x)`
(scalar-mult the covector).  Meromorphic because its chart coefficient is the product
`(f.toFun ∘ chart⁻¹) · formCoeff α`. -/
noncomputable def meroFormSMul (f : MeromorphicFunction X) (α : MeromorphicOneForm X) :
    MeromorphicOneForm X where
  toFun x := f.toFun x • α.toFun x
  meromorphic := by
    intro x
    have hcoeff : formCoeff (fun x => f.toFun x • α.toFun x) x
        = (f.toFun ∘ (chartAt ℂ x).symm) * formCoeff α.toFun x := by
      funext z; simp [formCoeff]
    rw [hcoeff]
    exact (f.meromorphic x).mul (α.meromorphic x)

@[simp] theorem meroFormSMul_toFun (f : MeromorphicFunction X) (α : MeromorphicOneForm X) (x : X) :
    (meroFormSMul f α).toFun x = f.toFun x • α.toFun x := rfl

/-- The chart coefficient of `f · α` is `(f ∘ chart⁻¹) · formCoeff α`. -/
theorem formCoeff_meroFormSMul (f : MeromorphicFunction X) (α : MeromorphicOneForm X) (x : X) :
    formCoeff (meroFormSMul f α).toFun x
      = (f.toFun ∘ (chartAt ℂ x).symm) * formCoeff α.toFun x := by
  funext z; simp [formCoeff, meroFormSMul]

/-- **Order additivity** (Forster 17.4): `formOrderW (f · α) x = orderW f x + formOrderW α x`. -/
theorem formOrderW_meroFormSMul (f : MeromorphicFunction X) (α : MeromorphicOneForm X) (x : X) :
    (meroFormSMul f α).formOrderW x = f.orderW x + α.formOrderW x := by
  rw [MeromorphicOneForm.formOrderW, formCoeff_meroFormSMul, MeromorphicFunction.orderW,
    MeromorphicOneForm.formOrderW]
  exact meromorphicOrderAt_mul (f.meromorphic x) (α.meromorphic x)

/-- **Forster 17.4 — `L(D) · Ω_E ⊆ Ω_{D+E}`.**  Multiplying a form in `Ω_E` by a function in `L(D)`
lands in `Ω_{D+E}`: orders add, and `−D ≤ orderW f`, `−E ≤ formOrderW α` give
`−(D+E) ≤ orderW f + formOrderW α`. -/
theorem meroFormSMul_mem_omegaD {D E : Divisor X} {f : MeromorphicFunction X}
    {α : MeromorphicOneForm X} (hf : f ∈ linearSystem (X := X) D) (hα : α ∈ omegaD (X := X) E) :
    meroFormSMul f α ∈ omegaD (X := X) (D + E) := by
  intro x
  rw [formOrderW_meroFormSMul]
  have h1 : (-(D x) : WithTop ℤ) ≤ f.orderW x := hf x
  have h2 : (-(E x) : WithTop ℤ) ≤ α.formOrderW x := hα x
  have hle : (-(D x) : WithTop ℤ) + (-(E x) : WithTop ℤ) ≤ f.orderW x + α.formOrderW x :=
    add_le_add h1 h2
  have heq : (-((D + E) x) : WithTop ℤ) = (-(D x) : WithTop ℤ) + (-(E x) : WithTop ℤ) := by
    rw [Finsupp.add_apply]; norm_cast; ring
  rw [heq]; exact hle

/-! ## Part 3: non-vacuity and the soundness anchor `Ω_0 ⊇ HolomorphicOneForms`

A holomorphic 1-form is a meromorphic 1-form (its coordinate coefficient `Montel.localRep ∘ chart⁻¹`
is analytic, hence meromorphic) with `formOrderW ≥ 0` (analytic functions have nonnegative
`meromorphicOrderAt`).  So every holomorphic form lands in `Ω_0`, and the constructed injection
`HolomorphicOneForms X → MeromorphicOneForm X` is the soundness check that `Ω_D` is the genuine
Forster object (Forster §17.4 at `D = 0`: `Ω_0 = H⁰(X, Ω) = HolomorphicOneForms`). -/

/-- The underlying section of a holomorphic 1-form, as a bare cotangent-bundle section.  (Forgets
smoothness; `HolomorphicOneForms X = ContMDiffSection …` coerces to its `toFun`.) -/
noncomputable def holToSection (α : HolomorphicOneForms X) : ∀ x, FormFiber X x := α.toFun

/-- The coordinate coefficient of a holomorphic form (via `holToSection`) is exactly the Montel /
`FormCoeff.coeffAt` coefficient. -/
theorem formCoeff_holToSection (α : HolomorphicOneForms X) (x : X) :
    formCoeff (holToSection α) x = coeffAt α x := by
  funext z; rfl

/-- A holomorphic 1-form is a meromorphic 1-form: its coordinate coefficient is analytic on the
chart target (`coeffAt_analyticOn`), hence meromorphic at every chart image. -/
theorem isMeromorphicOneForm_holToSection (α : HolomorphicOneForms X) :
    IsMeromorphicOneForm (holToSection α) := by
  intro x
  rw [formCoeff_holToSection]
  have hmem : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  exact (coeffAt_analyticAt α x hmem).meromorphicAt

/-- A holomorphic 1-form as a `MeromorphicOneForm`. -/
noncomputable def holToMero (α : HolomorphicOneForms X) : MeromorphicOneForm X :=
  ⟨holToSection α, isMeromorphicOneForm_holToSection α⟩

@[simp] theorem holToMero_toFun (α : HolomorphicOneForms X) :
    (holToMero α).toFun = α.toFun := rfl

/-- **`Ω_0` contains every holomorphic 1-form** — the order of a holomorphic form is `≥ 0`
everywhere (`AnalyticAt.meromorphicOrderAt_nonneg`). -/
theorem holToMero_mem_omegaD_zero (α : HolomorphicOneForms X) :
    holToMero α ∈ omegaD (X := X) 0 := by
  intro x
  have hz : (-(((0 : Divisor X) x)) : WithTop ℤ) = 0 := by simp
  rw [hz]
  show (0 : WithTop ℤ) ≤ meromorphicOrderAt (formCoeff (holToMero α).toFun x) ((chartAt ℂ x) x)
  rw [show (holToMero α).toFun = holToSection α from rfl, formCoeff_holToSection]
  have hmem : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  exact (coeffAt_analyticAt α x hmem).meromorphicOrderAt_nonneg

/-- **The holomorphic-to-meromorphic 1-form linear map.**  `holToMero` is ℂ-linear (the section
operations and `formCoeff` are pointwise-linear), giving `HolomorphicOneForms X →ₗ[ℂ]
MeromorphicOneForm X`.  This is the structure map of Forster §17.4 at `D = 0`. -/
noncomputable def holToMeroₗ : HolomorphicOneForms X →ₗ[ℂ] MeromorphicOneForm X where
  toFun := holToMero
  map_add' α β :=
    MeromorphicOneForm.ext (show holToSection (α + β) = holToSection α + holToSection β by
      funext x; exact congrFun (ContMDiffSection.coe_add α β) x)
  map_smul' c α :=
    MeromorphicOneForm.ext (show holToSection (c • α) = c • holToSection α by
      funext x; exact congrFun (ContMDiffSection.coe_smul c α) x)

@[simp] theorem holToMeroₗ_apply (α : HolomorphicOneForms X) : holToMeroₗ α = holToMero α := rfl

/-- `holToMeroₗ` is **injective**: equal underlying sections force equal holomorphic forms
(`ContMDiffSection.coe_injective`). -/
theorem holToMeroₗ_injective :
    Function.Injective (holToMeroₗ (X := X)) := by
  intro α β h
  apply ContMDiffSection.coe_injective
  have : (holToMero α).toFun = (holToMero β).toFun := congrArg MeromorphicOneForm.toFun h
  exact this

/-- **Non-vacuity / soundness anchor.**  `Ω_0` is non-trivial: it contains a faithful copy of the
kirovGenus-dimensional space of holomorphic 1-forms.  Concretely, `holToMeroₗ` is an injective ℂ-linear
map `HolomorphicOneForms X → MeromorphicOneForm X` whose image lies in `Ω_0`.  In particular, for an
effective `D` (all `0 ≤ D x`), `Ω_D ⊇ Ω_0 ⊇ HolomorphicOneForms`, so `Ω_D` is the genuine Forster
object, not a junk space. -/
theorem holToMero_mem_omegaD_of_effective {D : Divisor X} (hD : ∀ x, 0 ≤ D x)
    (α : HolomorphicOneForms X) : holToMero α ∈ omegaD (X := X) D := by
  have h0 : holToMero α ∈ omegaD (X := X) 0 := holToMero_mem_omegaD_zero α
  refine omegaD_mono ?_ h0
  intro x; simpa using hD x

/-! ### `Ω_0 ≅ HolomorphicOneForms` — the soundness check (Forster §17.4 at `D = 0`)

`Ω_0` (with the germ-junk quotiented out) is the genuine space of holomorphic 1-forms.  We prove the
solid direction `kirovGenus X ≤ omegaDim 0`: the holomorphic forms inject into the junk-free quotient
`omegaDModule 0`, because a holomorphic form that is germ-zero everywhere is the zero form (its
chart coefficient is analytic, and an analytic germ-zero function vanishes at its centre, so by the
identity theorem `exists_localRep_self_ne_zero` the section is `0`).  This is the non-vacuity /
soundness anchor: `omegaDim 0` is at least `kirovGenus X`, so `Ω_D ⊇ Ω_0` is the genuine §17.4 object. -/

/-- **A holomorphic form that is germ-zero everywhere is the zero form.**  At each `a`, the chart
coefficient `coeffAt α a` is analytic and (by `formOrderW = ⊤`) vanishes on a punctured
neighbourhood of `chart a a`, hence vanishes there too; so `localRep α a a = 0` for all `a`, whence
`α = 0` (contrapositive of `exists_localRep_self_ne_zero`). -/
theorem holToMero_eq_zero_of_germZero (α : HolomorphicOneForms X)
    (h : ∀ x, (holToMero α).formOrderW x = ⊤) : α = 0 := by
  by_contra hα
  obtain ⟨a, ha⟩ := exists_localRep_self_ne_zero α hα
  -- `coeffAt α a` is analytic at `chart a a`, with `meromorphicOrderAt = ⊤`.
  have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target :=
    (chartAt ℂ a).map_source (mem_chart_source ℂ a)
  have han : AnalyticAt ℂ (coeffAt α a) ((chartAt ℂ a) a) := coeffAt_analyticAt α a hmem
  have htop : meromorphicOrderAt (coeffAt α a) ((chartAt ℂ a) a) = ⊤ := by
    have := h a
    rwa [MeromorphicOneForm.formOrderW, show (holToMero α).toFun = holToSection α from rfl,
      formCoeff_holToSection] at this
  -- analytic order `⊤` ⇒ eventually zero on a full neighbourhood ⇒ value `0` at the centre.
  have hAtop : analyticOrderAt (coeffAt α a) ((chartAt ℂ a) a) = ⊤ := by
    have heq := han.meromorphicOrderAt_eq
    rw [htop] at heq
    exact ENat.map_eq_top_iff.mp heq.symm
  have hzero : coeffAt α a ((chartAt ℂ a) a) = 0 :=
    (analyticOrderAt_eq_top.mp hAtop).self_of_nhds
  rw [coeffAt_chartCenter] at hzero
  exact ha hzero

/-- The image of a holomorphic form under `holToMeroₗ`, as a member of the linear system `Ω_0`. -/
noncomputable def holInOmega0 (α : HolomorphicOneForms X) : ↥(omegaD (X := X) 0) :=
  ⟨holToMero α, holToMero_mem_omegaD_zero α⟩

/-- **The holomorphic-to-`Ω_0`-module linear map** `HolomorphicOneForms X → omegaDModule 0`:
`holToMeroₗ` landed in `Ω_0`, then projected to the junk-free quotient.  The structure map of
Forster §17.4 at `D = 0`; its injectivity gives `kirovGenus X ≤ omegaDim 0`. -/
noncomputable def holToOmega0Module : HolomorphicOneForms X →ₗ[ℂ] omegaDModule (X := X) 0 where
  toFun α := Submodule.Quotient.mk (holInOmega0 α)
  map_add' α β := by
    rw [← Submodule.Quotient.mk_add]; rfl
  map_smul' c α := by
    rw [← Submodule.Quotient.mk_smul]; rfl

/-- `holToOmega0Module` is **injective**: if `[holToMero α] = [holToMero β]` in the junk-free
quotient, then `holToMero (α − β)` is germ-zero everywhere, so `α − β = 0` by
`holToMero_eq_zero_of_germZero`. -/
theorem holToOmega0Module_injective :
    Function.Injective (holToOmega0Module (X := X)) := by
  rw [injective_iff_map_eq_zero]
  intro α hα
  -- `[holInOmega0 α] = 0` ⇒ `holInOmega0 α ∈ germ-zero submodule of Ω_0`.
  rw [holToOmega0Module, LinearMap.coe_mk, AddHom.coe_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.submoduleOf, Submodule.mem_comap] at hα
  -- `hα : (holInOmega0 α).1 ∈ formGermZeroSubmodule`, i.e. germ-zero everywhere.
  -- `(holInOmega0 α).1 = holToMero α`, so the identity theorem gives `α = 0`.
  exact holToMero_eq_zero_of_germZero α (fun x => hα x)

/-- **Soundness lower bound: `kirovGenus X ≤ omegaDim 0`** (when `Ω_0` is finite-dimensional).  The
kirovGenus-dimensional holomorphic forms inject into `omegaDModule 0` (`holToOmega0Module_injective`), so
`finrank` is monotone: `kirovGenus X ≤ omegaDim 0`.  This confirms `Ω_0` is the genuine Forster §17.4
object `H⁰(X, Ω)`, not a junk space.  (Finite-dimensionality of `Ω_0` is itself part of §17.4 —
`Ω_0 ≅ HolomorphicOneForms`, which is finite-dim; the bound is stated under that hypothesis so it
is unconditionally TRUE, avoiding the `finrank = 0` junk value of an a-priori unbounded quotient.) -/
theorem genus_le_omegaDim_zero [FiniteDimensional ℂ (omegaDModule (X := X) 0)] :
    kirovGenus X ≤ omegaDim (X := X) 0 :=
  calc kirovGenus X = finrank ℂ (HolomorphicOneForms X) := rfl
    _ ≤ finrank ℂ (omegaDModule (X := X) 0) :=
          LinearMap.finrank_le_finrank_of_injective holToOmega0Module_injective
    _ = omegaDim (X := X) 0 := rfl

/-- **The unconditional rank bound** `rank (HolomorphicOneForms) ≤ rank (omegaDModule 0)`.  The
honest junk-value-free soundness statement: the holomorphic forms inject into the meromorphic-1-form
quotient `Ω_0` (`holToOmega0Module_injective`), so its module rank is at least the kirovGenus rank — with
no finiteness hypothesis.  (Upgrades to `kirovGenus ≤ omegaDim 0` once `Ω_0` is known finite-dim.) -/
theorem rank_holomorphicOneForms_le_omega0 :
    Module.rank ℂ (HolomorphicOneForms X) ≤ Module.rank ℂ (omegaDModule (X := X) 0) :=
  holToOmega0Module.rank_le_of_injective holToOmega0Module_injective

/-- **`Ω_0 ≅ HolomorphicOneForms` (the full §17.4 soundness equality), conditional on the reverse
bound.**  `omegaDim 0 = kirovGenus X` follows from the proven lower bound `genus_le_omegaDim_zero`
together with the reverse `omegaDim 0 ≤ kirovGenus X`.  The reverse is the *removable-singularity*
direction: an order-`≥ 0` meromorphic 1-form has an analytic chart coefficient, so (modulo the
germ-junk it is quotiented by) it is a genuine holomorphic form — the analytic-to-smooth section
bridge.  This is the one isolated analytic input to the equality; the injection and the lower bound
are proven above. -/
theorem omegaDim_zero_eq_genus_of_le [FiniteDimensional ℂ (omegaDModule (X := X) 0)]
    (hle : omegaDim (X := X) 0 ≤ kirovGenus X) :
    omegaDim (X := X) 0 = kirovGenus X :=
  le_antisymm hle genus_le_omegaDim_zero

end Jacobians.Dolbeault
