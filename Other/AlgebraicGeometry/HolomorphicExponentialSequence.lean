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

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- A holomorphic function in the exponential kernel is locally a constant integral period. -/
theorem exists_integerPeriod_neighborhood
    (U : Opens (TopCat.of (ComplexPoint X)))
    (f : OpenHolomorphicFunctions X d (Opposite.op U))
    (hf : holomorphicExpUnit X d (Opposite.op U) f = 1) (x : U) :
    ∃ (V : Opens (TopCat.of (ComplexPoint X))) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ n : ℤ, holomorphicRestrictionAlgHom X d (homOfLE hVU).op f =
        algebraMap ℂ _ (n * (2 * Real.pi * Complex.I)) := by
  have hexp (y : U) : Complex.exp (f.1 y) = 1 :=
    congrArg (fun u : (OpenHolomorphicFunctions X d (Opposite.op U))ˣ => u.val.1 y) hf
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hexp x)
  let W : Set U := (fun y => (f.1 y - f.1 x).im) ⁻¹' Set.Ioo (-Real.pi) Real.pi
  have hW : IsOpen W := isOpen_Ioo.preimage (Complex.continuous_im.comp
    ((holomorphicFunctionSheaf_section_analytic X d f).continuous.sub continuous_const))
  let V : Opens (TopCat.of (ComplexPoint X)) :=
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
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  (Functor.const _).obj (AddCommGrpCat.of ℤ)

/-- The map sending an integer to the constant holomorphic function `2πi` times that integer. -/
def holomorphicIntegerPeriodPresheaf :
    integerPeriodSourcePresheaf X ⟶ holomorphicAdditiveFunctionPresheaf X d where
  app U := AddCommGrpCat.ofHom {
    toFun n := algebraMap ℂ (OpenHolomorphicFunctions X d U) (n * (2 * Real.pi * Complex.I))
    map_zero' := by simp
    map_add' m n := by simp [add_mul] }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    exact (holomorphicRestrictionAlgHom X d i).commutes _ |>.symm

/-- Integral periods exponentiate to the identity unit. -/
theorem holomorphicIntegerPeriodPresheaf_comp_exp :
    holomorphicIntegerPeriodPresheaf X d ≫ holomorphicExpPresheaf X d = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  change ℤ at n
  change holomorphicExpUnit X d U
    (algebraMap ℂ _ (((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩

/-- The integral-period map from the actual constant integer sheaf. -/
def holomorphicIntegerPeriodSheaf :
    constantIntegerSheaf X ⟶ holomorphicAdditiveFunctionSheaf X d :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicIntegerPeriodPresheaf X d) (holomorphicAdditiveFunctionSheaf X d).property⟩

/-- The sheaf map agrees with the displayed integral periods on constant sections. -/
@[reassoc (attr := simp)]
theorem toSheafify_comp_holomorphicIntegerPeriodSheaf :
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (integerPeriodSourcePresheaf X) ≫ (holomorphicIntegerPeriodSheaf X d).hom =
      holomorphicIntegerPeriodPresheaf X d :=
  toSheafify_sheafifyLift _ _ _

/-- The integral-period map and exponential form a complex of actual sheaves. -/
theorem holomorphicIntegerPeriodSheaf_comp_exp :
    holomorphicIntegerPeriodSheaf X d ≫ holomorphicExpSheaf X d = 0 := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      _ _ (holomorphicUnitsSheaf X d).property
  change toSheafify _ (integerPeriodSourcePresheaf X) ≫
      (holomorphicIntegerPeriodSheaf X d).hom ≫ holomorphicExpPresheaf X d = _
  rw [← Category.assoc, toSheafify_comp_holomorphicIntegerPeriodSheaf,
    holomorphicIntegerPeriodPresheaf_comp_exp]
  exact (Limits.comp_zero).symm

/-- The holomorphic exponential complex, with its integral normalization explicit. -/
def holomorphicExponentialSequence : ShortComplex (AnalyticAdditiveSheaf X) :=
  ShortComplex.mk (holomorphicIntegerPeriodSheaf X d) (holomorphicExpSheaf X d)
    (holomorphicIntegerPeriodSheaf_comp_exp X d)

/-- The integral-period sheaf map evaluated on an actual constant local section. -/
@[simp]
theorem holomorphicIntegerPeriodSheaf_app_toSheafify
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (n : ℤ) :
    (holomorphicIntegerPeriodSheaf X d).hom.app U
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (integerPeriodSourcePresheaf X)).app U n) =
      algebraMap ℂ (OpenHolomorphicFunctions X d U) (n * (2 * Real.pi * Complex.I)) := by
  exact congrArg (fun e => e.app U n)
    (toSheafify_comp_holomorphicIntegerPeriodSheaf X d)

/-- The exponential sequence is exact at the actual sheaf of holomorphic functions. -/
theorem holomorphicExponentialSequence_exact : (holomorphicExponentialSequence X d).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  apply holomorphicStalkExact_of_locallyPrimitive X
    ((holomorphicExponentialSequence X d).map
      (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint X)))) _ x
  intro y U hy f hf
  change holomorphicExpUnit X d (Opposite.op U) f = 1 at hf
  obtain ⟨V, hVU, hyV, n, hn⟩ := exists_integerPeriod_neighborhood X d U f hf ⟨y, hy⟩
  refine ⟨V, hyV, homOfLE hVU,
    (toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (integerPeriodSourcePresheaf X)).app (Opposite.op V) n, ?_⟩
  change (holomorphicIntegerPeriodSheaf X d).hom.app (Opposite.op V) _ =
    holomorphicRestrictionAlgHom X d (homOfLE hVU).op f
  rw [holomorphicIntegerPeriodSheaf_app_toSheafify]
  exact hn.symm

/-- Integral periods remain distinct on every stalk, since `2πi` is nonzero. -/
theorem holomorphicIntegerPeriodPresheaf_stalk_mono (x : ComplexPoint X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (holomorphicIntegerPeriodPresheaf X d)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b h
  obtain ⟨U, hxU, m, rfl⟩ := (integerPeriodSourcePresheaf X).exists_germ_eq a
  obtain ⟨V, hxV, n, rfl⟩ := (integerPeriodSourcePresheaf X).exists_germ_eq b
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iWU, iWV, hW⟩ := (holomorphicAdditiveFunctionPresheaf X d).germ_eq
    x hxU hxV ((holomorphicIntegerPeriodPresheaf X d).app (Opposite.op U) m)
      ((holomorphicIntegerPeriodPresheaf X d).app (Opposite.op V) n) h
  change ℤ at m n
  have hcoeff := congrArg
    (fun f : OpenHolomorphicFunctions X d (Opposite.op W) => f.1 ⟨x, hxW⟩) hW
  change (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
    (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) at hcoeff
  have hperiod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hmn : m = n := Int.cast_injective (mul_right_cancel₀ hperiod hcoeff)
  subst n
  rw [← (integerPeriodSourcePresheaf X).germ_res_apply iWU x hxW,
    ← (integerPeriodSourcePresheaf X).germ_res_apply iWV x hxW]
  rfl

/-- The integral-period morphism is a monomorphism of actual analytic sheaves. -/
instance holomorphicIntegerPeriodSheaf_mono : Mono (holomorphicIntegerPeriodSheaf X d) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let η := toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (integerPeriodSourcePresheaf X)
  let : IsIso (stalk.map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (integerPeriodSourcePresheaf X)
  let : Mono (stalk.map (holomorphicIntegerPeriodPresheaf X d)) :=
    holomorphicIntegerPeriodPresheaf_stalk_mono X d x
  have h : stalk.map (holomorphicIntegerPeriodSheaf X d).hom =
      inv (stalk.map η) ≫ stalk.map (holomorphicIntegerPeriodPresheaf X d) := by
    rw [← cancel_epi (stalk.map η), ← Functor.map_comp]
    change stalk.map
      (toSheafify _ (integerPeriodSourcePresheaf X) ≫ (holomorphicIntegerPeriodSheaf X d).hom) = _
    rw [toSheafify_comp_holomorphicIntegerPeriodSheaf]
    simp
  change Mono (stalk.map (holomorphicIntegerPeriodSheaf X d).hom)
  rw [h]
  infer_instance

/-- The holomorphic exponential sequence is short exact, with the genuine integral-period map
and the actual holomorphic exponential. -/
theorem holomorphicExponentialSequence_shortExact :
    (holomorphicExponentialSequence X d).ShortExact where
  exact := holomorphicExponentialSequence_exact X d
  mono_f := holomorphicIntegerPeriodSheaf_mono X d
  epi_g := holomorphicExpSheaf_epi X d

end AlgebraicGeometry.ComplexPoint
