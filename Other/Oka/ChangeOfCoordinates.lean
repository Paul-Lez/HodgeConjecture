/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Weierstrass

/-!
# Linear changes of coordinates on germs of holomorphic functions

The Weierstrass division and preparation theorems of `Other/Oka/Weierstrass.lean` apply to a germ
`f : LocalOkaRing (Fin (n + 1))` only under the hypothesis that `f` is *general* in the last
variable, i.e. that `f` does not vanish identically on the last coordinate axis. Classically
one removes that hypothesis by a linear change of coordinates: every nonzero germ becomes
general in the last variable after a suitable `ℂ`-linear automorphism of `ℂ^{n+1}`.

This file provides the germ-level change of coordinates and that genericity statement.
The corresponding manoeuvre one level up, for holomorphic functions on an open set, is
`OkaRing.congr` of `Other/Oka/StructureSheaf.lean` together with the argument inside
`exists_isWeierstrassPolynomial_row` of `Other/Oka/Statement.lean`.

## Main definitions

- `LocalOkaRing.congr`: the `ℂ`-algebra isomorphism `LocalOkaRing ι ≃ₐ[ℂ] LocalOkaRing κ`
  induced by a continuous linear equivalence `φ : ℂ^ι ≃L[ℂ] ℂ^κ`. It sends the germ at the
  origin of `f` to the germ at the origin of `f ∘ φ⁻¹`, matching the convention of
  `OkaRing.congr`.

## Main results

- `LocalOkaRing.congr_represents`: if `P` sums to `f` near the origin, then `congr φ P` sums to
  `f ∘ φ⁻¹` near the origin. This, together with the uniqueness statement
  `LocalOkaRing.congr_eq_of_represents`, is the characterisation every use of `congr` goes
  through.
- `LocalOkaRing.congr_germ` and `LocalOkaRing.congr_toLocalOkaRingHom`: taking germs commutes
  with changing coordinates.
- `LocalOkaRing.congr_refl` and `LocalOkaRing.congr_trans`: `congr` is functorial.
- `LocalOkaRing.congrEquiv`: the germ ring depends on the variables only through a bijection of
  the index type.
- `LocalOkaRing.exists_congr_isGeneralIn`: finitely many nonzero germs become simultaneously
  general in the last variable after a common linear change of coordinates, and its
  one-germ specialisation `LocalOkaRing.exists_congr_isGeneralIn_of_ne_zero`.
- `LocalOkaRing.exists_congr_localweierstrass_preparation`: Weierstrass preparation with the
  genericity hypothesis removed at the cost of a linear change of coordinates.

## Implementation notes

`LocalOkaRing.congr` is defined by choosing, for each `P`, *some* locally convergent power
series summing to `P.eval ∘ φ⁻¹` near the origin; this is possible because `P.eval` is
holomorphic at the origin and `φ⁻¹` is linear, hence entire, and fixes the origin. The choice
is immediately made irrelevant by the identity theorem `MvPowerSeries.Represents.unique`, and
no lemma below refers to it. Consequently every proof in the first section has the same shape:
exhibit a function which both sides sum to, and appeal to uniqueness.
-/

@[expose] public section

open Filter Topology TopologicalSpace MvPowerSeries

namespace LocalOkaRing

-- The section variables below are `Fintype` rather than `Finite`, matching the `OkaRing` and
-- `LocalOkaRing` API this file builds on: the norm on `ι → ℂ`, and hence every analyticity
-- statement used in the proofs, needs the `Fintype` data. That is a fact about the *proofs*,
-- not about the statements ; where a statement does not mention the norm, bind `[Finite ι]`
-- on the declaration and recover the data inside the proof with `Fintype.ofFinite`, as
-- `exists_represents_comp_symm` just below does.

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### The change of coordinates -/

section Congr

/-- The sum of a locally convergent power series, precomposed with a linear change of
coordinates, is again the sum of a locally convergent power series. -/
lemma exists_represents_comp_symm {ι κ : Type*} [Finite ι] [Finite κ]
    (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (P : LocalOkaRing ι) :
    ∃ Q : MvPowerSeries κ ℂ, Q.LocallyConvergent ∧
      Q.Represents ((P : MvPowerSeries ι ℂ).eval ∘ (φ.symm : (κ → ℂ) → (ι → ℂ))) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype κ := Fintype.ofFinite κ
  refine MvPowerSeries.exists_represents (AnalyticAt.comp ?_ ?_)
  · simpa using P.2.analyticAt
  · exact (φ.symm : (κ → ℂ) →L[ℂ] (ι → ℂ)).analyticAt 0

/-- The underlying function of `LocalOkaRing.congr`; an implementation detail, characterised by
`LocalOkaRing.congr_represents` and `LocalOkaRing.congr_eq_of_represents`. -/
noncomputable def congrAux (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (P : LocalOkaRing ι) : LocalOkaRing κ :=
  ⟨(exists_represents_comp_symm φ P).choose, (exists_represents_comp_symm φ P).choose_spec.1⟩

/-- `congrAux φ P` sums to `P.eval ∘ φ⁻¹` near the origin, by construction. -/
lemma congrAux_represents_eval (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) (P : LocalOkaRing ι) :
    ((congrAux φ P : LocalOkaRing κ) : MvPowerSeries κ ℂ).Represents
      ((P : MvPowerSeries ι ℂ).eval ∘ (φ.symm : (κ → ℂ) → (ι → ℂ))) :=
  (exists_represents_comp_symm φ P).choose_spec.2

/-- `congrAux φ P` sums to `f ∘ φ⁻¹` near the origin whenever `P` sums to `f`. -/
lemma congrAux_represents {φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)} {P : LocalOkaRing ι}
    {f : (ι → ℂ) → ℂ} (hf : (P : MvPowerSeries ι ℂ).Represents f) :
    ((congrAux φ P : LocalOkaRing κ) : MvPowerSeries κ ℂ).Represents
      (f ∘ (φ.symm : (κ → ℂ) → (ι → ℂ))) :=
  -- `φ.symm` is continuous and fixes the origin, so it tends to `0` at `0`
  (congrAux_represents_eval φ P).congr
    ((P.2.represents_eval.eventuallyEq hf).comp_tendsto
      (by simpa using φ.symm.continuous.tendsto (0 : κ → ℂ)))

/-- `congrAux φ P` is determined by summing to `f ∘ φ⁻¹`, for `f` any function that `P` sums
to; this is the identity theorem for convergent power series. -/
lemma congrAux_eq_of_represents {φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)} {P : LocalOkaRing ι}
    {Q : LocalOkaRing κ} {f : (ι → ℂ) → ℂ} (hP : (P : MvPowerSeries ι ℂ).Represents f)
    (hQ : (Q : MvPowerSeries κ ℂ).Represents (f ∘ (φ.symm : (κ → ℂ) → (ι → ℂ)))) :
    congrAux φ P = Q :=
  Subtype.ext ((congrAux_represents hP).unique hQ)

/-- A `ℂ`-linear change of coordinates `φ : ℂ^ι ≃ ℂ^κ` identifies the germs at the origin of
holomorphic functions on `ℂ^ι` with those on `ℂ^κ`, by `f ↦ f ∘ φ⁻¹`.

This is the germ-level counterpart of `OkaRing.congr`, and follows the same convention: the
germ of `f` is sent to the germ of `f ∘ φ⁻¹`, not of `f ∘ φ`. -/
noncomputable def congr (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) : LocalOkaRing ι ≃ₐ[ℂ] LocalOkaRing κ where
  toFun := congrAux φ
  invFun := congrAux φ.symm
  left_inv P := by
    refine congrAux_eq_of_represents (congrAux_represents_eval φ P) ?_
    have h : ((P : MvPowerSeries ι ℂ).eval ∘ (φ.symm : (κ → ℂ) → (ι → ℂ))) ∘
        (φ.symm.symm : (ι → ℂ) → (κ → ℂ)) = (P : MvPowerSeries ι ℂ).eval := by
      funext x
      simp
    rw [h]
    exact P.2.represents_eval
  right_inv Q := by
    refine congrAux_eq_of_represents (congrAux_represents_eval φ.symm Q) ?_
    have h : ((Q : MvPowerSeries κ ℂ).eval ∘ (φ.symm.symm : (ι → ℂ) → (κ → ℂ))) ∘
        (φ.symm : (κ → ℂ) → (ι → ℂ)) = (Q : MvPowerSeries κ ℂ).eval := by
      funext x
      simp
    rw [h]
    exact Q.2.represents_eval
  map_mul' P Q :=
    congrAux_eq_of_represents
      (Represents.mul P.2 Q.2 P.2.represents_eval Q.2.represents_eval)
      (Represents.mul (congrAux φ P).2 (congrAux φ Q).2
        (congrAux_represents_eval φ P) (congrAux_represents_eval φ Q))
  map_add' P Q :=
    congrAux_eq_of_represents (P.2.represents_eval.add Q.2.represents_eval)
      ((congrAux_represents_eval φ P).add (congrAux_represents_eval φ Q))
  commutes' c :=
    congrAux_eq_of_represents (represents_algebraMap (ι := ι) c)
      (represents_algebraMap (ι := κ) c)

/-- Changing coordinates back along `φ` is changing coordinates along `φ⁻¹`. -/
@[simp]
lemma congr_symm (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) : (congr φ).symm = congr φ.symm :=
  rfl

/-- The germ `congr φ P` sums to `f ∘ φ⁻¹` near the origin whenever `P` sums to `f`. -/
lemma congr_represents {φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)} {P : LocalOkaRing ι} {f : (ι → ℂ) → ℂ}
    (hf : (P : MvPowerSeries ι ℂ).Represents f) :
    ((congr φ P : LocalOkaRing κ) : MvPowerSeries κ ℂ).Represents
      (f ∘ (φ.symm : (κ → ℂ) → (ι → ℂ))) :=
  congrAux_represents hf

/-- `congr φ P` is the unique germ summing to `f ∘ φ⁻¹` near the origin, for `f` any function
that `P` sums to. -/
lemma congr_eq_of_represents {φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)} {P : LocalOkaRing ι}
    {Q : LocalOkaRing κ} {f : (ι → ℂ) → ℂ} (hP : (P : MvPowerSeries ι ℂ).Represents f)
    (hQ : (Q : MvPowerSeries κ ℂ).Represents (f ∘ (φ.symm : (κ → ℂ) → (ι → ℂ)))) :
    congr φ P = Q :=
  congrAux_eq_of_represents hP hQ

/-- The identity change of coordinates does nothing. -/
@[simp]
lemma congr_refl (P : LocalOkaRing ι) :
    congr (ContinuousLinearEquiv.refl ℂ (ι → ℂ)) P = P :=
  congr_eq_of_represents (f := (P : MvPowerSeries ι ℂ).eval) P.2.represents_eval
    P.2.represents_eval

/-- Changing coordinates twice is changing coordinates once. -/
lemma congr_trans {μ : Type*} [Fintype μ] (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ))
    (ψ : (κ → ℂ) ≃L[ℂ] (μ → ℂ)) (P : LocalOkaRing ι) :
    congr (φ.trans ψ) P = congr ψ (congr φ P) := by
  refine congr_eq_of_represents (f := (P : MvPowerSeries ι ℂ).eval) P.2.represents_eval ?_
  have h : (P : MvPowerSeries ι ℂ).eval ∘ ((φ.trans ψ).symm : (μ → ℂ) → (ι → ℂ)) =
      ((P : MvPowerSeries ι ℂ).eval ∘ (φ.symm : (κ → ℂ) → (ι → ℂ))) ∘
        (ψ.symm : (μ → ℂ) → (κ → ℂ)) := by
    funext x
    simp
  rw [h]
  exact congr_represents (congr_represents P.2.represents_eval)

/-- Relabelling the variables identifies the germ rings: a bijection `ι ≃ κ` induces the
`ℂ`-linear change of coordinates permuting the coordinates of `ℂ^ι`, hence a `ℂ`-algebra
isomorphism of the germ rings at the origin. -/
noncomputable def congrEquiv (e : ι ≃ κ) :
    LocalOkaRing ι ≃ₐ[ℂ] LocalOkaRing κ :=
  congr (LinearEquiv.toContinuousLinearEquiv (LinearEquiv.funCongrLeft ℂ ℂ e.symm))

end Congr

/-! ### Compatibility with taking germs -/

section Germ

variable (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ)) {U : Opens (ι → ℂ)} {y : ι → ℂ}

/-- Taking germs commutes with a linear change of coordinates. -/
lemma congr_germ (hy : y ∈ U) (f : OkaRing U) :
    congr φ (OkaRing.germ hy f) =
      OkaRing.germ (show φ y ∈ φ.opensCongr U by simpa using hy) (OkaRing.congr φ U f) := by
  refine (OkaRing.germ_eq_of_represents _ ?_).symm
  refine (congr_represents (OkaRing.germ_represents hy f)).congr ?_
  -- both sides sum to `w ↦ f (φ⁻¹ w + y)` near the origin
  have hmem : (0 : κ → ℂ) ∈ (φ.opensCongr U).shift (φ y) := by simpa using hy
  filter_upwards [((φ.opensCongr U).shift (φ y)).isOpen.mem_nhds hmem] with w hw
  have hwU : w + φ y ∈ φ.opensCongr U := hw
  have hsymm : φ.symm (w + φ y) = φ.symm w + y := by
    simp [map_add]
  rw [Function.comp_apply, (OkaRing.congr φ U f).toGlobalFun_apply hwU,
    f.toGlobalFun_apply (show φ.symm w + y ∈ U from hsymm ▸ hwU)]
  exact _root_.congrArg (f.toFun _) (Subtype.ext hsymm.symm)

/-- Taking Taylor series at the origin commutes with a linear change of coordinates. -/
lemma congr_toLocalOkaRingHom (h0 : (0 : ι → ℂ) ∈ U) (f : OkaRing U) :
    congr φ (OkaRing.toLocalOkaRingHom U h0 f) =
      OkaRing.toLocalOkaRingHom (φ.opensCongr U)
        (show (0 : κ → ℂ) ∈ φ.opensCongr U by simpa using h0) (OkaRing.congr φ U f) := by
  refine (OkaRing.toLocalOkaRing_eq_of_represents
    (h0 := show (0 : κ → ℂ) ∈ φ.opensCongr U by simpa using h0) ?_).symm
  refine (congr_represents (f.toLocalOkaRing_represents h0)).congr ?_
  refine (OkaRing.toGlobalFun_eventuallyEq
    (show (0 : κ → ℂ) ∈ φ.opensCongr U by simpa using h0)
    (f := OkaRing.congr φ U f)
    (g := f.toGlobalFun _ ∘ (φ.symm : (κ → ℂ) → (ι → ℂ))) fun x ↦ ?_).symm
  exact (f.toGlobalFun_apply (show φ.symm (x : κ → ℂ) ∈ U from x.2)).symm

end Germ

/-! ### Making a germ general in the last variable -/

section IsGeneralIn

variable {n : ℕ}

/-- Finitely many nonzero germs become simultaneously general in the last variable after a
common linear change of coordinates of `ℂ^{n+1}`.

This is the germ-level form of the manoeuvre carried out for holomorphic functions inside
`exists_isWeierstrassPolynomial_row`. -/
theorem exists_congr_isGeneralIn {p : ℕ} (f : Fin p → LocalOkaRing (Fin (n + 1)))
    (hf : ∀ i, f i ≠ 0) :
    ∃ φ : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ), ∀ i,
      ((congr φ (f i) : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (Fin.last n) := by
  classical
  have hcoe : ∀ i, ((f i : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ) ≠ 0 :=
    fun i hc ↦ hf i (Subtype.ext hc)
  obtain ⟨v, hvlast, hv⟩ := MvPowerSeries.exists_direction
    (fun i ↦ ((f i : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) hcoe
  refine ⟨lineEquiv v hvlast, fun i hgen ↦ ?_⟩
  -- the germ, read in the new coordinates, vanishes on the last axis near the origin
  have hax := (congr_represents (φ := lineEquiv v hvlast)
    (f i).2.represents_eval).eventually_axis_eq_zero (Fin.last n) hgen
  -- pulling back, the germ itself vanishes on the line spanned by `v` near the origin
  have hline : ∀ᶠ t : ℂ in 𝓝 (0 : ℂ),
      ((f i : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ).eval (t • v) = 0 := by
    filter_upwards [hax] with t ht
    rwa [Function.comp_apply, lineEquiv_symm_smul_single v hvlast t] at ht
  -- but then every homogeneous part of the germ vanishes at `v`, contradicting the choice of `v`
  obtain ⟨k, hk⟩ := hv i
  exact hk ((f i).2.represents_eval.homogeneous_eval_eq_zero v hline k)

/-- A nonzero germ becomes general in the last variable after a linear change of coordinates. -/
theorem exists_congr_isGeneralIn_of_ne_zero {f : LocalOkaRing (Fin (n + 1))} (hf : f ≠ 0) :
    ∃ φ : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ),
      ((congr φ f : LocalOkaRing (Fin (n + 1))) :
        MvPowerSeries (Fin (n + 1)) ℂ).IsGeneralIn (Fin.last n) := by
  obtain ⟨φ, hφ⟩ := exists_congr_isGeneralIn (fun _ : Fin 1 ↦ f) fun _ ↦ hf
  exact ⟨φ, hφ 0⟩

/-- The Weierstrass preparation theorem for an arbitrary nonzero germ: after a linear change of
coordinates, every nonzero germ is a unit times a Weierstrass polynomial.

This is `localweierstrass_preparation` with its genericity hypothesis removed, which is the
form needed whenever one starts from an arbitrary element of `LocalOkaRing (Fin (n + 1))`. -/
theorem exists_congr_localweierstrass_preparation {f : LocalOkaRing (Fin (n + 1))}
    (hf : f ≠ 0) :
    ∃ (φ : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)) (u : LocalOkaRing (Fin (n + 1)))
      (_ : IsUnit u) (g : Polynomial (LocalOkaRing (Fin n)))
      (_ : IsLocalWeierstrassPolynomial
        (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) g)),
      congr φ f = LocalOkaRing.fromPolynomial g * u := by
  obtain ⟨φ, hφ⟩ := exists_congr_isGeneralIn_of_ne_zero hf
  exact ⟨φ, localweierstrass_preparation _ hφ⟩

end IsGeneralIn

end LocalOkaRing

end
