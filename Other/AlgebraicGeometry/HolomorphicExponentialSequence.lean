/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponential
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# The holomorphic exponential sequence

The integer inclusion and the normalized exponential give the short exact sequence
`0 → ℤ → 𝒪 → 𝒪ˣ → 0` on the analytic complex-point space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category Limits TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

local instance holomorphicExponentialSequenceTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- Integer constants as sections of the holomorphic-function presheaf. -/
def integerConstantsToHolomorphicPresheaf :
    (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶
      (holomorphicAdditiveSheaf X d).obj where
  app U := AddCommGrpCat.ofHom
    (ContMDiffMap.C.toAddMonoidHom.comp (Int.castAddHom ℂ))
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    apply ContMDiffMap.ext
    intro x
    rfl

/-- The canonical inclusion of the constant integer sheaf into holomorphic functions. -/
def integerConstantsToHolomorphicSheaf :
    constantIntegerSheaf X ⟶ holomorphicAdditiveSheaf X d :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (integerConstantsToHolomorphicPresheaf X d) (holomorphicAdditiveSheaf X d).property⟩

@[reassoc (attr := simp)]
lemma toSheafify_integerConstantsToHolomorphicSheaf :
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        ((Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (AddCommGrpCat.of ℤ)) ≫
      (integerConstantsToHolomorphicSheaf X d).hom =
        integerConstantsToHolomorphicPresheaf X d :=
  toSheafify_sheafifyLift ..

lemma integerConstantsToHolomorphicPresheaf_comp_exponential :
    integerConstantsToHolomorphicPresheaf X d ≫ (holomorphicExponential X d).hom = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  change ℤ at n
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  change Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1
  rw [mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I n

set_option backward.isDefEq.respectTransparency false in
lemma integerConstantsToHolomorphicSheaf_comp_exponential :
    integerConstantsToHolomorphicSheaf X d ≫ holomorphicExponential X d = 0 := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (holomorphicUnitSheaf X d).property
  change _ ≫ (integerConstantsToHolomorphicSheaf X d).hom ≫
    (holomorphicExponential X d).hom = _ ≫ 0
  rw [← Category.assoc, toSheafify_integerConstantsToHolomorphicSheaf,
    integerConstantsToHolomorphicPresheaf_comp_exponential, comp_zero]

/-- The exponential short complex before sheafifying its constant integer term. -/
def holomorphicExponentialPresheafSequence :
    ShortComplex (TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  ShortComplex.mk (integerConstantsToHolomorphicPresheaf X d)
    (holomorphicExponential X d).hom
    (integerConstantsToHolomorphicPresheaf_comp_exponential X d)

/-- The exponential sequence of analytic sheaves. -/
def holomorphicExponentialSequence :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  ShortComplex.mk (integerConstantsToHolomorphicSheaf X d) (holomorphicExponential X d)
    (integerConstantsToHolomorphicSheaf_comp_exponential X d)

set_option backward.isDefEq.respectTransparency false in
/-- Sheafifying the integer term leaves the other two terms unchanged. -/
def holomorphicExponentialSequenceSheafificationUnit :
    holomorphicExponentialPresheafSequence X d ⟶
      (holomorphicExponentialSequence X d).map
        (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint X))) where
  τ₁ := toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    change _ ≫ (integerConstantsToHolomorphicSheaf X d).hom =
      integerConstantsToHolomorphicPresheaf X d ≫ 𝟙 _
    rw [comp_id]
    exact toSheafify_integerConstantsToHolomorphicSheaf X d
  comm₂₃ := by
    rw [id_comp, comp_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The exponential sequence is exact on every stalk before sheafifying its first term. -/
theorem holomorphicExponentialPresheafSequence_stalk_exact (x : ComplexPoint X) :
    ((holomorphicExponentialPresheafSequence X d).map
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact := by
  apply holomorphicStalkExact_of_locallyPrimitive
  intro y U hy f hf
  change C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯ at f
  change ContMDiffMap.holomorphicExponential f = 0 at hf
  have he : ∀ z : U, Complex.exp (2 * Real.pi * Complex.I * f z) = 1 := by
    intro z
    exact congrArg
      (fun t : Additive (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)ˣ ↦
        (t.toMul : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) z) hf
  obtain ⟨V, hVU, hyV, n, hn⟩ := f.exists_local_eq_int ⟨y, hy⟩ he
  refine ⟨V, hyV, homOfLE hVU, n, ?_⟩
  apply ContMDiffMap.ext
  intro z
  exact (hn z).symm

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the holomorphic exponential is the constant integer sheaf. -/
theorem holomorphicExponentialSequence_exact : (holomorphicExponentialSequence X d).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let η := (stalk.mapShortComplex).map (holomorphicExponentialSequenceSheafificationUnit X d)
  have : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat _
  have : IsIso η.τ₂ := by
    change IsIso (stalk.map (𝟙 _))
    rw [stalk.map_id]
    infer_instance
  have : IsIso η.τ₃ := by
    change IsIso (stalk.map (𝟙 _))
    rw [stalk.map_id]
    infer_instance
  have : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η)
    (holomorphicExponentialPresheafSequence_stalk_exact X d x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integer constants remain distinct as germs of holomorphic functions. -/
theorem integerConstantsToHolomorphicPresheaf_stalk_mono (x : ComplexPoint X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (integerConstantsToHolomorphicPresheaf X d)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  let P : TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
    (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj (AddCommGrpCat.of ℤ)
  intro z z' h
  obtain ⟨U, hxU, n, rfl⟩ := P.exists_germ_eq z
  obtain ⟨V, hxV, n', rfl⟩ := P.exists_germ_eq z'
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
    (holomorphicAdditiveSheaf X d).presheaf.germ_eq x hxU hxV _ _ h
  change ℤ at n n'
  have hn : (n : ℤ) = n' := by
    have hc := congrArg
      (fun f : C^ω⟮𝓘(ℂ, Fin d → ℂ), W; ℂ⟯ ↦ f ⟨x, hxW⟩) hW
    change ((n : ℤ) : ℂ) = ((n' : ℤ) : ℂ) at hc
    exact Int.cast_injective hc
  subst n'
  rw [← P.germ_res_apply iWU x hxW, ← P.germ_res_apply iWV x hxW]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constant integer sheaf embeds into the holomorphic-function sheaf. -/
instance integerConstantsToHolomorphicSheaf_mono :
    Mono (integerConstantsToHolomorphicSheaf X d) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let S := (holomorphicExponentialPresheafSequence X d).map stalk
  let T := (holomorphicExponentialSequence X d).map
    (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ComplexPoint X)) ⋙ stalk)
  let η : S ⟶ T :=
    (stalk.mapShortComplex).map (holomorphicExponentialSequenceSheafificationUnit X d)
  have : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat _
  have : IsIso η.τ₂ := by
    change IsIso (stalk.map (𝟙 _))
    rw [stalk.map_id]
    infer_instance
  have : Mono S.f := integerConstantsToHolomorphicPresheaf_stalk_mono X d x
  change Mono T.f
  have h : T.f = inv η.τ₁ ≫ S.f ≫ η.τ₂ := by
    rw [← cancel_epi η.τ₁, η.comm₁₂]
    simp
  rw [h]
  infer_instance

/-- The holomorphic exponential sequence `0 → ℤ → 𝒪 → 𝒪ˣ → 0` is short exact. -/
theorem holomorphicExponentialSequence_shortExact :
    (holomorphicExponentialSequence X d).ShortExact where
  exact := holomorphicExponentialSequence_exact X d
  mono_f := integerConstantsToHolomorphicSheaf_mono X d
  epi_g := holomorphicExponential_epi X d

end AlgebraicGeometry.ComplexPoint
