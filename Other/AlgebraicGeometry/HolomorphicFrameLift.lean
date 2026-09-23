/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionCorrectedLiftsOfIso

/-!
# Lifts attached to holomorphic frames

A generating section of the line bundle of a unit-sheaf extension determines a lift of
the constant integer section `1`. The construction is independent of the chosen canonical
local frame and commutes with restriction. Multiplication of the generating section by a
unit adds that unit's image under the extension inclusion to its lift. This fixes the sign
needed when comparing a regular frame with the frame of a rational Cartier section.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff
namespace AlgebraicGeometry.ComplexPoint
variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
local instance frameLiftTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- A unit multiple of a generating holomorphic section generates. -/
lemma HolomorphicGenerates.isUnit_smul
    {M : SheafOfModules (holomorphicRingSheaf X d)}
    {U : Opens (TopCat.of (ComplexPoint X))} {s : M.val.obj (op U)}
    (hs : HolomorphicGenerates s) {v : (holomorphicRingSheaf X d).obj.obj (op U)}
    (hv : IsUnit v) : HolomorphicGenerates (v • s) := by
  intro V h
  have hfun : (fun r : (holomorphicRingSheaf X d).obj.obj (op V) ↦
      r • holRes M h (v • s)) =
      (fun r : (holomorphicRingSheaf X d).obj.obj (op V) ↦ r • holRes M h s) ∘
        fun r ↦ r * (holomorphicRingSheaf X d).obj.map (homOfLE h).op v := by
    funext r
    rw [Function.comp_apply, holRes_smul, mul_smul]
  rw [hfun]
  exact (hs V h).comp
    (IsUnit.isUnit_iff_mulRight_bijective.mp
      (hv.map ((holomorphicRingSheaf X d).obj.map (homOfLE h).op).hom))

namespace HolomorphicUnitExtension
variable (E : HolomorphicUnitExtension X d)

/-- The unique unit carrying a given frame to a canonical extension frame. -/
def frameLiftUnit (z : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens z)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s) :
    (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)ˣ :=
  (hs.exists_isUnit_smul_eq (E.holomorphicGenerates_frame z U hU)).choose_spec.1.unit

lemma frameLiftUnit_smul (z : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens z)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s) :
    unitSection (E.frameLiftUnit z U hU s hs) • s = E.frame z U hU := by
  have h := (hs.exists_isUnit_smul_eq (E.holomorphicGenerates_frame z U hU)).choose_spec.2
  rw [← (hs.exists_isUnit_smul_eq (E.holomorphicGenerates_frame z U hU)).choose_spec.1.unit_spec] at h
  exact h

lemma frameLiftUnit_unique (z : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens z)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s)
    (u : (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)ˣ)
    (hu : unitSection u • s = E.frame z U hU) : E.frameLiftUnit z U hU s hs = u := by
  apply Units.ext
  exact hs.bijective.injective ((E.frameLiftUnit_smul z U hU s hs).trans hu.symm)

/-- The lift of `1` associated with a generating holomorphic section. -/
def frameLift (z : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens z)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s) :
    E.middle.obj.obj (op U) :=
  sres E.middle hU (E.localLifts.lift z) -
    E.inclusion.hom.app (op U) (Additive.ofMul (E.frameLiftUnit z U hU s hs))

lemma projection_frameLift (z : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens z)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s) :
    E.projection.hom.app (op U) (E.frameLift z U hU s hs) = integerOneRestrict X U := by
  unfold frameLift
  rw [map_sub]
  erw [inclusion_projection_apply, sub_zero]
  exact E.localLifts.map_restrictLift z U hU

lemma frameLiftUnit_smul_unit (z : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens z)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s)
    (u : (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)ˣ) :
    E.frameLiftUnit z U hU (unitSection u • s) (hs.isUnit_smul u.isUnit) * u =
      E.frameLiftUnit z U hU s hs := by
  apply Units.ext
  apply hs.bijective.injective
  change (_ * unitSection u) • s = unitSection (E.frameLiftUnit z U hU s hs) • s
  rw [mul_smul]
  exact (E.frameLiftUnit_smul z U hU _ (hs.isUnit_smul u.isUnit)).trans
    (E.frameLiftUnit_smul z U hU s hs).symm

/-- Multiplying a frame by a unit adds the unit to the associated extension lift. -/
lemma frameLift_smul_unit (z : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens z)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s)
    (u : (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)ˣ) :
    E.frameLift z U hU (unitSection u • s) (hs.isUnit_smul u.isUnit) =
      E.frameLift z U hU s hs + E.inclusion.hom.app (op U) (Additive.ofMul u) := by
  have h := congrArg Additive.ofMul (E.frameLiftUnit_smul_unit z U hU s hs u)
  change Additive.ofMul (E.frameLiftUnit z U hU (unitSection u • s) (hs.isUnit_smul u.isUnit)) + Additive.ofMul u =
    Additive.ofMul (E.frameLiftUnit z U hU s hs) at h
  unfold frameLift
  erw [← h, map_add]
  erw [sub_add_eq_sub_sub, sub_add_cancel]
  rfl

lemma frameLiftUnit_restrict (z : ComplexPoint X)
    {U V : Opens (TopCat.of (ComplexPoint X))} (hU : U ≤ E.localLifts.opens z) (hVU : V ≤ U)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s) :
    Additive.ofMul (E.frameLiftUnit z V (hVU.trans hU)
      (holRes E.sectionSheafOfModules hVU s) (hs.restrict hVU)) =
      sres (holomorphicUnitSheaf X d) hVU (Additive.ofMul (E.frameLiftUnit z U hU s hs)) := by
  have h := congrArg (holRes E.sectionSheafOfModules hVU)
    (E.frameLiftUnit_smul z U hU s hs)
  rw [holRes_smul, E.holRes_frame] at h
  apply Additive.toMul.injective
  exact E.frameLiftUnit_unique z V (hVU.trans hU) _ (hs.restrict hVU) _ h

/-- Restriction of frames commutes with their associated extension lifts. -/
lemma frameLift_restrict (z : ComplexPoint X)
    {U V : Opens (TopCat.of (ComplexPoint X))} (hU : U ≤ E.localLifts.opens z) (hVU : V ≤ U)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s) :
    E.frameLift z V (hVU.trans hU)
      (holRes E.sectionSheafOfModules hVU s) (hs.restrict hVU) =
      sres E.middle hVU (E.frameLift z U hU s hs) := by
  unfold frameLift
  erw [E.frameLiftUnit_restrict z hU hVU s hs]
  have hsub : ∀ a b : E.middle.obj.obj (op U),
      sres E.middle hVU (a - b) = sres E.middle hVU a - sres E.middle hVU b :=
    fun a b => map_sub _ _ _
  rw [hsub, sres_sres, sres_hom]

/-- The lift of a frame is independent of the canonical frame used to construct it. -/
lemma frameLift_eq (z w : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hz : U ≤ E.localLifts.opens z) (hw : U ≤ E.localLifts.opens w)
    (s : E.sectionSheafOfModules.val.obj (op U)) (hs : HolomorphicGenerates s) :
    E.frameLift z U hz s hs = E.frameLift w U hw s hs := by
  have hu : E.frameLiftUnit w U hw s hs =
      E.transitionUnit w z U hw hz * E.frameLiftUnit z U hz s hs := by
    apply E.frameLiftUnit_unique w U hw s hs
    change (unitSection (E.transitionUnit w z U hw hz) *
      unitSection (E.frameLiftUnit z U hz s hs)) • s = _
    rw [mul_smul, E.frameLiftUnit_smul]
    exact E.smul_frame z w U hz hw
  have ha := congrArg Additive.ofMul hu
  change Additive.ofMul (E.frameLiftUnit w U hw s hs) =
    Additive.ofMul (E.transitionUnit w z U hw hz) +
      Additive.ofMul (E.frameLiftUnit z U hz s hs) at ha
  have ht : E.inclusion.hom.app (op U) (Additive.ofMul (E.transitionUnit w z U hw hz)) =
      sres E.middle hw (E.localLifts.lift w) - sres E.middle hz (E.localLifts.lift z) :=
    E.localLifts.transition_spec E.shortExact w z U hw hz
  unfold frameLift
  erw [ha, map_add, ht]
  exact (show ∀ a b c : E.middle.obj.obj (op U), a - b = c - (c - a + b) by
    intros; abel) _ _ _

end HolomorphicUnitExtension
end AlgebraicGeometry.ComplexPoint
