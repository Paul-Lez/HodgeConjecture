/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Evaluation
public import Other.Oka.Analytification.GAGA.HolomorphicFrechetOps

/-!
# Sections of the structure sheaf over chart images

Let `Z` be a complex analytic space and `φ : ℂⁿ ⟶ Z` a chart, i.e. an open immersion of analytic
spaces. For an open `V ⊆ ℂⁿ` the sections of `𝒪_Z` over `φ(V)` are the holomorphic functions on
`V` (`ComplexAnalytic.chartRingEquiv`), compatibly with restriction, with the
constants, and with values at points.

For two charts `φ, φ'` and opens `V, V'` with `φ'(V') ⊆ φ(V)`, restriction
`𝒪_Z(φ(V)) → 𝒪_Z(φ'(V'))` read in the charts is composition with the transition map, a
holomorphic map `V' → V`; in particular it is **continuous** for the topology of compact
convergence (`ComplexAnalytic.chartRestrictCLM`). No explicit formula for
the transition map is needed: it is recovered from the values of the restricted coordinate
functions.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

namespace ComplexAnalytic

namespace AnalyticSpace

variable {n : ℕ}

/-- **On `ℂⁿ` the value of a section over an open `U` is its value as a holomorphic
function.** -/
theorem eval_complexAffineSpace_apply {U : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)}
    (y : AnalyticSpace.complexAffineSpace.{u} n) (hy : y ∈ U) (s : OkaRing U) :
    (AnalyticSpace.complexAffineSpace.{u} n).eval (U := U) y hy s =
      OkaRing.evalHom (U := U) (x := y) hy s := by
  set c := OkaRing.evalHom (U := U) (x := y) hy s with hc
  refine ((AnalyticSpace.complexAffineSpace.{u} n).evalStalk_eq_iff _ _).2 ?_
  rw [AnalyticSpace.stalkAlgMap, LocallyRingedSpace.stalkAlgMap_apply,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE le_top) y hy]
  erw [← map_sub]
  refine (germ_mem_maximalIdeal_iff (ι := ULift.{u} (Fin n)) (y := y) (U := U) hy _).2 ?_
  refine (map_sub (OkaRing.evalHom (U := U) (x := y) hy) _ _).trans (sub_eq_zero.2 ?_)
  refine hc.symm.trans ?_
  change c = OkaRing.evalHom hy
    (OkaRing.restrict le_top (Algebra.algebraMap (R := ℂ) (A := OkaRing ⊤) c))
  rw [AlgHom.commutes, OkaRing.evalHom_algebraMap]

/-- Evaluation commutes with restriction. -/
lemma eval_map {Z : AnalyticSpace.{u}} {U V : TopologicalSpace.Opens Z} (h : V ≤ U) (z : Z)
    (hz : z ∈ V) (s : Z.presheaf.obj (op U)) :
    Z.eval z hz (Z.presheaf.map (homOfLE h).op s) = Z.eval z (h hz) s := by
  rw [eval_apply, eval_apply, TopCat.Presheaf.germ_res_apply]

end AnalyticSpace

/-- Two restrictions of a section of the structure sheaf of a locally ringed space compose. -/
lemma presheaf_map_map {Y : LocallyRingedSpace.{u}} {U V W : Opens Y} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (h₃ : W ≤ U) (s : Y.presheaf.obj (op U)) :
    Y.presheaf.map (homOfLE h₁).op (Y.presheaf.map (homOfLE h₂).op s) =
      Y.presheaf.map (homOfLE h₃).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

section Chart

variable {Z : AnalyticSpace.{u}} {n : ℕ} (φ : AnalyticSpace.complexAffineSpace.{u} n ⟶ Z)
  [LocallyRingedSpace.IsOpenImmersion φ.toLRSHom]

/-- The image `φ(V)` of an open `V ⊆ ℂⁿ` under a chart. -/
noncomputable abbrev chartOpen (V : Opens (ULift.{u} (Fin n) → ℂ)) : Opens Z.toPresheafedSpace :=
  (LocallyRingedSpace.IsOpenImmersion.opensFunctor φ.toLRSHom).obj V

variable {φ} in
lemma chartOpen_mono {V V' : Opens (ULift.{u} (Fin n) → ℂ)} (h : V' ≤ V) :
    chartOpen φ V' ≤ chartOpen φ V :=
  (LocallyRingedSpace.IsOpenImmersion.opensFunctor φ.toLRSHom).monotone h

/-- **Sections of `𝒪_Z` over a chart image are holomorphic functions**: for a chart
`φ : ℂⁿ ⟶ Z` and `V ⊆ ℂⁿ` open, `𝒪(V) ≃ 𝒪_Z(φ(V))`. -/
noncomputable def chartRingEquiv (V : Opens (ULift.{u} (Fin n) → ℂ)) :
    OkaRing V ≃+* Z.presheaf.obj (op (chartOpen φ V)) :=
  (asIso (LocallyRingedSpace.IsOpenImmersion.invApp φ.toLRSHom V)).commRingCatIsoToRingEquiv

lemma chartRingEquiv_apply (V : Opens (ULift.{u} (Fin n) → ℂ)) (f : OkaRing V) :
    chartRingEquiv φ V f = LocallyRingedSpace.IsOpenImmersion.invApp φ.toLRSHom V f :=
  rfl

/-- The identification of sections over chart images commutes with restriction. -/
lemma chartRingEquiv_restrict {V V' : Opens (ULift.{u} (Fin n) → ℂ)} (h : V' ≤ V)
    (f : OkaRing V) :
    chartRingEquiv φ V' (OkaRing.restrict h f) =
      Z.presheaf.map (homOfLE (chartOpen_mono h)).op (chartRingEquiv φ V f) := by
  have := ConcreteCategory.congr_hom
    (LocallyRingedSpace.IsOpenImmersion.inv_naturality φ.toLRSHom (homOfLE h).op) f
  exact this

/-- The identification of sections over chart images is `ℂ`-linear: it sends the constant `c`
to the restriction of the constant `c` of `Z`. -/
lemma chartRingEquiv_algebraMap (V : Opens (ULift.{u} (Fin n) → ℂ)) (c : ℂ) :
    chartRingEquiv φ V (Algebra.algebraMap (R := ℂ) (A := OkaRing V) c) =
      Z.presheaf.map (homOfLE le_top).op (Z.algebraMap c) := by
  have h1 : (Algebra.algebraMap (R := ℂ) (A := OkaRing V) c) = OkaRing.restrict
      (le_top : V ≤ (Opens.map φ.toLRSHom.base).obj ⊤)
      (φ.toLRSHom.c.app (op ⊤) (Z.algebraMap c)) := by
    have h2 : φ.toLRSHom.c.app (op ⊤) (Z.algebraMap c) =
        Algebra.algebraMap (R := ℂ) (A := OkaRing ⊤) c := φ.isCLinear c
    rw [h2]
    exact ((OkaRing.restrict _).commutes c).symm
  rw [h1, chartRingEquiv_restrict, chartRingEquiv_apply]
  have h3 := ConcreteCategory.congr_hom
    (LocallyRingedSpace.IsOpenImmersion.app_invApp φ.toLRSHom ⊤) (Z.algebraMap c)
  rw [ConcreteCategory.comp_apply] at h3
  erw [h3]
  exact presheaf_map_map _ _ _ _

/-- **Values of sections over chart images**: the value at `φ y` of the section corresponding
to a holomorphic function `f` is `f y`. -/
lemma eval_chartRingEquiv (V : Opens (ULift.{u} (Fin n) → ℂ)) (f : OkaRing V)
    {y : ULift.{u} (Fin n) → ℂ} (hy : y ∈ V) :
    Z.eval (U := chartOpen φ V) (φ.toLRSHom.base y) ⟨y, hy, rfl⟩ (chartRingEquiv φ V f) =
      OkaRing.evalHom hy f := by
  have h := AnalyticSpace.eval_c_app φ.toLRSHom φ.isCLinear (U := chartOpen φ V) y ⟨y, hy, rfl⟩
    (chartRingEquiv φ V f)
  rw [← h, chartRingEquiv_apply]
  have h4 := ConcreteCategory.congr_hom
    (LocallyRingedSpace.IsOpenImmersion.invApp_app φ.toLRSHom V) f
  rw [ConcreteCategory.comp_apply] at h4
  rw [h4]
  exact (AnalyticSpace.eval_complexAffineSpace_apply _ _ _).trans
    (OkaRing.evalHom_restrict _ _ f)

end Chart

section Transition

variable {Z : AnalyticSpace.{u}} {n : ℕ} (φ φ' : AnalyticSpace.complexAffineSpace.{u} n ⟶ Z)
  [LocallyRingedSpace.IsOpenImmersion φ.toLRSHom] [LocallyRingedSpace.IsOpenImmersion φ'.toLRSHom]
  {V V' : Opens (ULift.{u} (Fin n) → ℂ)} (h : chartOpen φ' V' ≤ chartOpen φ V)

/-- **Restriction between chart images, in the charts**: `𝒪(V) ≃ 𝒪_Z(φ(V)) → 𝒪_Z(φ'(V'))
≃ 𝒪(V')` for `φ'(V') ⊆ φ(V)`. -/
noncomputable def chartRestrict : OkaRing V →+* OkaRing V' :=
  (chartRingEquiv φ' V').symm.toRingHom.comp
    ((Z.presheaf.map (homOfLE h).op).hom.comp (chartRingEquiv φ V).toRingHom)

lemma chartRingEquiv_chartRestrict (f : OkaRing V) :
    chartRingEquiv φ' V' (chartRestrict φ φ' h f) =
      Z.presheaf.map (homOfLE h).op (chartRingEquiv φ V f) :=
  (chartRingEquiv φ' V').apply_symm_apply _

/-- The transition map `φ⁻¹ ∘ φ'` of two charts (defined by `Function.invFun` off the image). -/
noncomputable def transition (y : ULift.{u} (Fin n) → ℂ) : ULift.{u} (Fin n) → ℂ :=
  Function.invFun φ.toLRSHom.base (φ'.toLRSHom.base y)

variable {φ φ'}

set_option linter.unusedSectionVars false in
include h in
lemma transition_spec {y : ULift.{u} (Fin n) → ℂ} (hy : y ∈ V') :
    φ.toLRSHom.base (transition φ φ' y) = φ'.toLRSHom.base y ∧ transition φ φ' y ∈ V := by
  obtain ⟨x, hx, hxy⟩ := h ⟨y, hy, rfl⟩
  have h₁ : φ.toLRSHom.base (transition φ φ' y) = φ'.toLRSHom.base y :=
    Function.invFun_eq ⟨x, hxy⟩
  refine ⟨h₁, ?_⟩
  have : transition φ φ' y = x :=
    (PresheafedSpace.IsOpenImmersion.base_open (f := φ.toLRSHom.toHom)).injective
      (h₁.trans hxy.symm)
  exact this ▸ hx

/-- Values do not depend on the proof of membership, and only on the point. -/
lemma eval_eq_of_point_eq {U : Opens Z.toPresheafedSpace} {z z' : Z} (hzz' : z = z')
    (hz : z ∈ U) (hz' : z' ∈ U) (s : Z.presheaf.obj (op U)) : Z.eval z hz s = Z.eval z' hz' s := by
  subst hzz'
  rfl

include h in
/-- **The restriction between chart images is composition with the transition map**, on
values. -/
lemma evalHom_chartRestrict (f : OkaRing V) {y : ULift.{u} (Fin n) → ℂ} (hy : y ∈ V') :
    OkaRing.evalHom hy (chartRestrict φ φ' h f) =
      OkaRing.evalHom (transition_spec h hy).2 f := by
  rw [← eval_chartRingEquiv φ' V' _ hy, chartRingEquiv_chartRestrict]
  refine (AnalyticSpace.eval_map _ _ _ _).trans ?_
  rw [← eval_chartRingEquiv φ V f (transition_spec h hy).2]
  exact eval_eq_of_point_eq (transition_spec h hy).1.symm _ _ _

include h in
/-- The transition map is holomorphic on `V'`. -/
lemma differentiableOn_transition : DifferentiableOn ℂ (transition φ φ') V' := by
  refine differentiableOn_pi.2 fun j ↦ ?_
  let coord : OkaRing V := OkaRing.ofDifferentiableOn (fun z ↦ z j)
    (differentiable_apply j).differentiableOn
  refine (chartRestrict φ φ' h coord).differentiableOn_toGlobalFun.congr fun y hy ↦ ?_
  rw [OkaRing.toGlobalFun_apply _ hy, ← OkaRing.evalHom_apply, evalHom_chartRestrict h coord hy,
    OkaRing.evalHom_apply]
  rfl

include h in
lemma mapsTo_transition : Set.MapsTo (transition φ φ') V' V := fun _ hy ↦
  (transition_spec h hy).2

/-- The restriction between chart images is composition with the (holomorphic) transition map. -/
lemma chartRestrict_eq_comp (f : OkaRing V) :
    chartRestrict φ φ' h f = OkaRing.comp (transition φ φ') (differentiableOn_transition h)
      (mapsTo_transition h) f := by
  refine OkaRing.ext (funext fun y ↦ ?_)
  rw [OkaRing.comp_toFun, ← OkaRing.evalHom_apply, evalHom_chartRestrict h f y.2,
    OkaRing.evalHom_apply]

/-- **Restriction between chart images is continuous** for the topologies of compact
convergence, as a `ℂ`-linear map. -/
noncomputable def chartRestrictCLM : OkaRing V →L[ℂ] OkaRing V' :=
  (OkaRing.compCLM (transition φ φ') (differentiableOn_transition h) (mapsTo_transition h))

lemma chartRestrictCLM_apply (f : OkaRing V) :
    chartRestrictCLM h f = chartRestrict φ φ' h f :=
  (chartRestrict_eq_comp h f).symm

end Transition

end ComplexAnalytic

end
