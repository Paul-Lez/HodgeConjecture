/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLocalLogarithm
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

import Mathlib.Topology.Sheaves.Sheafify

/-!
# The holomorphic exponential sequence

The exponential kernel is locally the integral multiples of `2 * π * I`. The maps in this
file use the actual constant integer sheaf, holomorphic functions, and holomorphic units on the
complex points of a smooth scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

/-- A holomorphic function in the exponential kernel is locally a constant integral period. -/
theorem exists_integerPeriod_neighborhood
    (U : Opens (TopCat.of (ComplexPoint X s)))
    (f : OpenHolomorphicFunctions s d (Opposite.op U))
    (hf : holomorphicExpUnit s d (Opposite.op U) f = 1) (x : U) :
    ∃ (V : Opens (TopCat.of (ComplexPoint X s))) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ n : ℤ, holomorphicRestrictionAlgHom s d (homOfLE hVU).op f =
        algebraMap ℂ _ (n * (2 * Real.pi * Complex.I)) := by
  have hexp (y : U) : Complex.exp (f.1 y) = 1 :=
    congrArg (fun u : (OpenHolomorphicFunctions s d (Opposite.op U))ˣ => u.val.1 y) hf
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hexp x)
  let W : Set U := (fun y => (f.1 y - f.1 x).im) ⁻¹' Set.Ioo (-Real.pi) Real.pi
  have hW : IsOpen W := isOpen_Ioo.preimage (Complex.continuous_im.comp
    ((holomorphicFunctionSheaf_section_analytic s d f).continuous.sub continuous_const))
  let V : Opens (TopCat.of (ComplexPoint X s)) :=
    ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩
  have hVU : V ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact z.2
  have hxV : x.1 ∈ V :=
    ⟨x, by change (f.1 x - f.1 x).im ∈ Set.Ioo (-Real.pi) Real.pi
           simpa using Real.pi_pos, rfl⟩
  refine ⟨V, hVU, hxV, n, ?_⟩
  apply ContMDiffMap.ext
  intro y
  rcases y.2 with ⟨z, hz, heq⟩
  have hyz : (⟨y.1, hVU y.2⟩ : U) = z := Subtype.ext heq.symm
  change f.1 ⟨y.1, hVU y.2⟩ = n * (2 * Real.pi * Complex.I)
  rw [hyz, ← hn]
  apply sub_eq_zero.mp
  apply Complex.exp_inj_of_neg_pi_lt_of_le_pi hz.1 hz.2.le
    (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)
  rw [Complex.exp_sub, hexp z, hexp x, Complex.exp_zero, div_one]

/-- Constant integers regarded as a presheaf before sheafification. -/
abbrev integerPeriodSourcePresheaf :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X s)) :=
  (Functor.const _).obj (AddCommGrpCat.of ℤ)

/-- The map sending an integer to the constant holomorphic function `2πi` times that integer. -/
def holomorphicIntegerPeriodPresheaf :
    integerPeriodSourcePresheaf s ⟶ holomorphicAdditiveFunctionPresheaf s d where
  app U := AddCommGrpCat.ofHom {
    toFun n := algebraMap ℂ (OpenHolomorphicFunctions s d U) (n * (2 * Real.pi * Complex.I))
    map_zero' := by simp
    map_add' m n := by simp [add_mul] }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    exact (holomorphicRestrictionAlgHom s d i).commutes _ |>.symm

/-- Integral periods exponentiate to the identity unit. -/
theorem holomorphicIntegerPeriodPresheaf_comp_exp :
    holomorphicIntegerPeriodPresheaf s d ≫ holomorphicExpPresheaf s d = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  change ℤ at n
  change holomorphicExpUnit s d U
    (algebraMap ℂ _ (((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩

/-- The integral-period map from the actual constant integer sheaf. -/
def holomorphicIntegerPeriodSheaf :
    constantIntegerSheaf s ⟶ holomorphicAdditiveFunctionSheaf s d :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
    (holomorphicIntegerPeriodPresheaf s d) (holomorphicAdditiveFunctionSheaf s d).property⟩

/-- The sheaf map agrees with the displayed integral periods on constant sections. -/
@[reassoc (attr := simp)]
theorem toSheafify_comp_holomorphicIntegerPeriodSheaf :
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
        (integerPeriodSourcePresheaf s) ≫ (holomorphicIntegerPeriodSheaf s d).hom =
      holomorphicIntegerPeriodPresheaf s d :=
  toSheafify_sheafifyLift _ _ _

/-- The integral-period map and exponential form a complex of actual sheaves. -/
theorem holomorphicIntegerPeriodSheaf_comp_exp :
    holomorphicIntegerPeriodSheaf s d ≫ holomorphicExpSheaf s d = 0 := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
      _ _ (holomorphicUnitsSheaf s d).property
  change toSheafify _ (integerPeriodSourcePresheaf s) ≫
      (holomorphicIntegerPeriodSheaf s d).hom ≫ holomorphicExpPresheaf s d = _
  rw [← Category.assoc, toSheafify_comp_holomorphicIntegerPeriodSheaf,
    holomorphicIntegerPeriodPresheaf_comp_exp]
  exact (Limits.comp_zero).symm

/-- The holomorphic exponential complex, with its integral normalization explicit. -/
def holomorphicExponentialSequence : ShortComplex (AnalyticAdditiveSheaf s) :=
  ShortComplex.mk (holomorphicIntegerPeriodSheaf s d) (holomorphicExpSheaf s d)
    (holomorphicIntegerPeriodSheaf_comp_exp s d)

/-- The integral-period sheaf map evaluated on an actual constant local section. -/
@[simp]
theorem holomorphicIntegerPeriodSheaf_app_toSheafify
    (U : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) (n : ℤ) :
    (holomorphicIntegerPeriodSheaf s d).hom.app U
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
        (integerPeriodSourcePresheaf s)).app U n) =
      algebraMap ℂ (OpenHolomorphicFunctions s d U) (n * (2 * Real.pi * Complex.I)) := by
  exact congrArg (fun e => e.app U n)
    (toSheafify_comp_holomorphicIntegerPeriodSheaf s d)

/-- The exponential sequence is exact at the actual sheaf of holomorphic functions. -/
theorem holomorphicExponentialSequence_exact : (holomorphicExponentialSequence s d).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  apply holomorphicStalkExact_of_locallyPrimitive s
    ((holomorphicExponentialSequence s d).map
      (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint X s)))) _ x
  intro y U hy f hf
  change holomorphicExpUnit s d (Opposite.op U) f = 1 at hf
  obtain ⟨V, hVU, hyV, n, hn⟩ := exists_integerPeriod_neighborhood s d U f hf ⟨y, hy⟩
  refine ⟨V, hyV, homOfLE hVU,
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
      (integerPeriodSourcePresheaf s)).app (Opposite.op V) n, ?_⟩
  change (holomorphicIntegerPeriodSheaf s d).hom.app (Opposite.op V) _ =
    holomorphicRestrictionAlgHom s d (homOfLE hVU).op f
  rw [holomorphicIntegerPeriodSheaf_app_toSheafify]
  exact hn.symm

/-- Integral periods remain distinct on every stalk, since `2πi` is nonzero. -/
theorem holomorphicIntegerPeriodPresheaf_stalk_mono (x : ComplexPoint X s) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (holomorphicIntegerPeriodPresheaf s d)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b h
  obtain ⟨U, hxU, m, rfl⟩ := (integerPeriodSourcePresheaf s).exists_germ_eq a
  obtain ⟨V, hxV, n, rfl⟩ := (integerPeriodSourcePresheaf s).exists_germ_eq b
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iWU, iWV, hW⟩ := (holomorphicAdditiveFunctionPresheaf s d).germ_eq
    x hxU hxV ((holomorphicIntegerPeriodPresheaf s d).app (Opposite.op U) m)
      ((holomorphicIntegerPeriodPresheaf s d).app (Opposite.op V) n) h
  change ℤ at m n
  have hcoeff := congrArg
    (fun f : OpenHolomorphicFunctions s d (Opposite.op W) => f.1 ⟨x, hxW⟩) hW
  change (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
    (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) at hcoeff
  have hperiod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hmn : m = n := Int.cast_injective (mul_right_cancel₀ hperiod hcoeff)
  subst n
  rw [← (integerPeriodSourcePresheaf s).germ_res_apply iWU x hxW,
    ← (integerPeriodSourcePresheaf s).germ_res_apply iWV x hxW]
  rfl

/-- The integral-period morphism is a monomorphism of actual analytic sheaves. -/
instance holomorphicIntegerPeriodSheaf_mono : Mono (holomorphicIntegerPeriodSheaf s d) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let η := toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
    (integerPeriodSourcePresheaf s)
  let : IsIso (stalk.map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (integerPeriodSourcePresheaf s)
  let : Mono (stalk.map (holomorphicIntegerPeriodPresheaf s d)) :=
    holomorphicIntegerPeriodPresheaf_stalk_mono s d x
  have h : stalk.map (holomorphicIntegerPeriodSheaf s d).hom =
      inv (stalk.map η) ≫ stalk.map (holomorphicIntegerPeriodPresheaf s d) := by
    rw [← cancel_epi (stalk.map η), ← Functor.map_comp]
    change stalk.map
      (toSheafify _ (integerPeriodSourcePresheaf s) ≫ (holomorphicIntegerPeriodSheaf s d).hom) = _
    rw [toSheafify_comp_holomorphicIntegerPeriodSheaf]
    simp
  change Mono (stalk.map (holomorphicIntegerPeriodSheaf s d).hom)
  rw [h]
  infer_instance

/-- The holomorphic exponential sequence is short exact, with the genuine integral-period map
and the actual holomorphic exponential. -/
theorem holomorphicExponentialSequence_shortExact :
    (holomorphicExponentialSequence s d).ShortExact where
  exact := holomorphicExponentialSequence_exact s d
  mono_f := holomorphicIntegerPeriodSheaf_mono s d
  epi_g := holomorphicExpSheaf_epi s d

end AlgebraicGeometry.ComplexPoint
