/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Regular.Free
public import Other.Oka.Algebra.Category.ModuleCat.ProjectiveDimension

/-!
# Projective dimension and quotients by a regular element

Let `R` be a Noetherian local ring and `x ∈ 𝔪` a nonzerodivisor. If every finitely generated
`R ⧸ (x)`-module has projective dimension `≤ d`, then every finitely generated `R`-module has
projective dimension `≤ d + 1` (`ModuleCat.HasFGGlobalDimensionLE.of_quotient`).

The proof is Kaplansky's change of rings: for a finitely generated `R`-module `K` on which `x` is
regular, `pd_R K ≤ pd_{R ⧸ (x)} (K ⧸ x K)` (`ModuleCat.hasProjectiveDimensionLE_of_quotSMulTop`),
by induction on the right hand side. For `0` it is `Module.free_quotSMulTop_iff_free` (Nakayama);
for the inductive step, a presentation `0 → L → Rᵏ → K → 0` stays exact modulo `x` because `x`
is regular on `K`. A first syzygy of any finitely generated module is `x`-regular, which gives
the statement.

## Main definitions and results

* `ModuleCat.HasFGGlobalDimensionLE R d`: every finitely generated `R`-module has projective
  dimension `≤ d`.
* `ModuleCat.HasFGGlobalDimensionLE.of_ringEquiv`: invariance under ring isomorphisms.
* `ModuleCat.hasProjectiveDimensionLE_of_quotSMulTop`: change of rings.
* `ModuleCat.HasFGGlobalDimensionLE.of_quotient`: the global statement.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace ModuleCat

/-- Every finitely generated `R`-module (in the universe of `R`) has projective dimension at
most `d`. -/
def HasFGGlobalDimensionLE (R : Type u) [CommRing R] (d : ℕ) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    HasProjectiveDimensionLE (ModuleCat.of R M) d

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Bounds on the projective dimension of finitely generated modules are invariant under ring
isomorphisms. -/
lemma HasFGGlobalDimensionLE.of_ringEquiv {R R' : Type u} [CommRing R] [CommRing R']
    (e : R ≃+* R') {d : ℕ} (h : HasFGGlobalDimensionLE R d) : HasFGGlobalDimensionLE R' d := by
  intro M _ _ _
  letI : Module R M := Module.compHom M (e : R →+* R')
  haveI : Module.Finite R M := by
    obtain ⟨s, hs⟩ := ‹Module.Finite R' M›.fg_top
    refine ⟨⟨s, Submodule.eq_top_iff'.2 fun m ↦ ?_⟩⟩
    have hm : m ∈ Submodule.span R' (s : Set M) := hs ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy =>
      have : r • y = e.symm r • y := by
        change r • y = e (e.symm r) • y
        rw [RingEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.smul_mem _ _ hy
  let e' : ModuleCat.of R M ≃ₛₗ[RingHomClass.toRingHom e] ModuleCat.of R' M :=
    { AddEquiv.refl M with map_smul' := fun _ _ ↦ rfl }
  have := h M
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e e' d

/-- A field has finitely generated global dimension `0`. -/
lemma hasFGGlobalDimensionLE_zero_of_isField {R : Type u} [CommRing R] (hR : IsField R) :
    HasFGGlobalDimensionLE R 0 := by
  letI := hR.toField
  intro M _ _ _
  simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective]
  infer_instance

variable {R : Type u} [CommRing R]

/-- A first syzygy of a module is `x`-regular as soon as `R` is. -/
lemma isSMulRegular_ker {k : ℕ} {M : Type u} [AddCommGroup M] [Module R M]
    (f : (Fin k → R) →ₗ[R] M) {x : R} (hx : IsSMulRegular R x) :
    IsSMulRegular (LinearMap.ker f) x := by
  intro a b hab
  refine Subtype.ext (funext fun i ↦ hx ?_)
  have := congrArg (fun c : LinearMap.ker f ↦ (c : Fin k → R) i) hab
  simpa using this

section Local

variable [IsLocalRing R] [IsNoetherianRing R] {x : R}

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- The sequence `0 → L ⧸ x L → F ⧸ x F → K ⧸ x K` obtained from `0 → L → F → K` is injective
on the left when `x` is regular on `K`. -/
lemma injective_quotSMulTop_map_subtype_ker {F K : Type u} [AddCommGroup F] [Module R F]
    [AddCommGroup K] [Module R K] (f : F →ₗ[R] K) (hK : IsSMulRegular K x) :
    Function.Injective (QuotSMulTop.map x (LinearMap.ker f).subtype) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hq
  have hfv : f v = 0 := by
    refine hK.right_eq_zero_of_smul ?_
    rw [← map_smul, hv]
    exact l.2
  rw [Submodule.Quotient.mk_eq_zero]
  have : l = x • (⟨v, hfv⟩ : LinearMap.ker f) := Subtype.ext (by simpa using hv.symm)
  rw [this]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- **Change of rings for projective dimension.** Let `x ∈ 𝔪` be a nonzerodivisor of the
Noetherian local ring `R` and `K` a finitely generated `R`-module on which `x` is regular. If
`K ⧸ x K` has projective dimension `≤ e` over `R ⧸ (x)`, then `K` has projective dimension `≤ e`
over `R`. -/
theorem hasProjectiveDimensionLE_of_quotSMulTop (hreg : IsSMulRegular R x)
    (hx : x ∈ maximalIdeal R) (e : ℕ) :
    ∀ (K : Type u) [AddCommGroup K] [Module R K] [Module.Finite R K], IsSMulRegular K x →
      HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x K)) e →
      HasProjectiveDimensionLE (ModuleCat.of R K) e := by
  induction e with
  | zero =>
    intro K _ _ _ hK h
    haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.2 fun htop ↦ (maximalIdeal.isMaximal R).ne_top
        (eq_top_iff.2 (htop ▸ Ideal.span_le.2 (by simpa using hx)))
    haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    haveI : Module.Projective (R ⧸ Ideal.span {x}) (QuotSMulTop x K) :=
      projective_of_hasProjectiveDimensionLE_zero _
    haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x K) :=
      Module.Finite.of_restrictScalars_finite R _ _
    haveI : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x K) :=
      Module.free_of_flat_of_isLocalRing
    haveI := Module.finitePresentation_of_finite R K
    have hjac : x ∈ (⊥ : Ideal R).jacobson := by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    haveI : Module.Free R K := (Module.free_quotSMulTop_iff_free R K hjac hK).1 inferInstance
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
      ← IsProjective.iff_projective]
    infer_instance
  | succ e ih =>
    intro K _ _ _ hK h
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R K
    have hLreg : IsSMulRegular (LinearMap.ker f) x := isSMulRegular_ker f hreg
    let S := R ⧸ Ideal.span {x}
    let i : QuotSMulTop x (LinearMap.ker f) →ₗ[S] QuotSMulTop x (Fin k → R) :=
      (QuotSMulTop.map x (LinearMap.ker f).subtype).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective
    let p : QuotSMulTop x (Fin k → R) →ₗ[S] QuotSMulTop x K :=
      (QuotSMulTop.map x f).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    have hex : Function.Exact i p :=
      QuotSMulTop.map_exact x (LinearMap.exact_subtype_ker_map f) hf
    have hi : Function.Injective i := injective_quotSMulTop_map_subtype_ker f hK
    have hp : Function.Surjective p := QuotSMulTop.map_surjective x hf
    haveI : HasProjectiveDimensionLE (ModuleCat.of S (QuotSMulTop x K)) (e + 1) := h
    have hL := hasProjectiveDimensionLE_of_exact i p hex hi hp e
    haveI := ih (LinearMap.ker f) hLreg hL
    exact hasProjectiveDimensionLE_succ_of_exact (LinearMap.ker f).subtype f
      (LinearMap.exact_subtype_ker_map f) (Submodule.injective_subtype _) hf e

/-- **Global dimension and quotients by a regular element.** If `x ∈ 𝔪` is a nonzerodivisor of
the Noetherian local ring `R` and every finitely generated `R ⧸ (x)`-module has projective
dimension `≤ d`, then every finitely generated `R`-module has projective dimension `≤ d + 1`. -/
theorem HasFGGlobalDimensionLE.of_quotient (hreg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R)
    {d : ℕ} (h : HasFGGlobalDimensionLE (R ⧸ Ideal.span {x}) d) :
    HasFGGlobalDimensionLE R (d + 1) := by
  intro M _ _ _
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x (LinearMap.ker f)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  haveI := hasProjectiveDimensionLE_of_quotSMulTop hreg hx d (LinearMap.ker f)
    (isSMulRegular_ker f hreg) (h _)
  exact hasProjectiveDimensionLE_succ_of_exact (LinearMap.ker f).subtype f
    (LinearMap.exact_subtype_ker_map f) (Submodule.injective_subtype _) hf d

end Local

end ModuleCat

end
