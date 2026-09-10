/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionMiddleHom
public import Other.AlgebraicGeometry.HolomorphicLineBundleFrame

/-!
# Corrected lifts from an isomorphism of section sheaves

An isomorphism between the sheaves of sections of the line bundles of two unit-sheaf extensions
gives, on the common lifting neighbourhoods, a `0`-cochain of invertible holomorphic functions
whose coboundary is the quotient of the two transition cocycles. Correcting the local lifts of
`1` in the second extension by that cochain produces a `CorrectedLifts` datum.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open HolomorphicUnitExtension

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance unitExtensionCorrectedLiftsOfIsoTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- The invertible holomorphic function underlying a section of the unit sheaf. -/
abbrev unitOf {U : Opens (TopCat.of (ComplexPoint X))}
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) : (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯)ˣ :=
  Additive.toMul a

theorem unitOf_add {U : Opens (TopCat.of (ComplexPoint X))}
    (a b : (holomorphicUnitSheaf X d).obj.obj (op U)) : unitOf (a + b) = unitOf a * unitOf b := rfl

theorem unitOf_injective {U : Opens (TopCat.of (ComplexPoint X))}
    {a b : (holomorphicUnitSheaf X d).obj.obj (op U)}
    (h : ∀ y : U, (unitOf a).val y = (unitOf b).val y) : a = b := by
  have : unitOf a = unitOf b := Units.ext (ContMDiffMap.ext h)
  exact Additive.toMul.injective this

theorem unitOf_sres_val {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (a : (holomorphicUnitSheaf X d).obj.obj (op U)) (y : V) :
    (unitOf (sres (holomorphicUnitSheaf X d) h a)).val y = (unitOf a).val ⟨y, h y.property⟩ := rfl

theorem unitOf_transition (E : HolomorphicUnitExtension X d) (z w : ComplexPoint X)
    (V : Opens (TopCat.of (ComplexPoint X))) (hz : V ≤ E.localLifts.opens z)
    (hw : V ≤ E.localLifts.opens w) :
    unitOf (E.localLifts.transition E.shortExact z w V hz hw) = E.transitionUnit z w V hz hw := rfl

namespace CorrectedLifts

/-- Corrected lifts built from a `0`-cochain of holomorphic units whose coboundary is the
difference of the two transition cocycles. -/
def ofUnitCochain (E E' : HolomorphicUnitExtension X d)
    (W : ComplexPoint X → Opens (TopCat.of (ComplexPoint X)))
    (hmem : ∀ z, z ∈ W z) (hWE : ∀ z, W z ≤ E.localLifts.opens z)
    (hWE' : ∀ z, W z ≤ E'.localLifts.opens z)
    (γ : ∀ z, (holomorphicUnitSheaf X d).obj.obj (op (W z)))
    (hγ : ∀ (z w : ComplexPoint X) (V : Opens (TopCat.of (ComplexPoint X)))
      (hz : V ≤ W z) (hw : V ≤ W w),
      sres (holomorphicUnitSheaf X d) hz (γ z) +
          E'.localLifts.transition E'.shortExact z w V (hz.trans (hWE' z)) (hw.trans (hWE' w)) =
        sres (holomorphicUnitSheaf X d) hw (γ w) +
          E.localLifts.transition E.shortExact z w V (hz.trans (hWE z)) (hw.trans (hWE w))) :
    CorrectedLifts E E' where
  opens := W
  mem_opens := hmem
  le_opens := hWE
  lift z := sres E'.middle (hWE' z) (E'.localLifts.lift z) +
    E'.inclusion.hom.app (op (W z)) (γ z)
  map_lift z := by
    rw [hom_add, inclusion_projection_apply, add_zero]
    exact E'.localLifts.map_restrictLift z (W z) (hWE' z)
  sub_lift z w V hz hw := by
    have hl : sres E'.middle (hz.trans (hWE' z)) (E'.localLifts.lift z) -
        sres E'.middle (hw.trans (hWE' w)) (E'.localLifts.lift w) =
        E'.inclusion.hom.app (op V) (E'.localLifts.transition E'.shortExact z w V
          (hz.trans (hWE' z)) (hw.trans (hWE' w))) :=
      (E'.localLifts.transition_spec E'.shortExact z w V _ _).symm
    have hg2 : E'.inclusion.hom.app (op V) (sres (holomorphicUnitSheaf X d) hz (γ z)) +
        E'.inclusion.hom.app (op V) (E'.localLifts.transition E'.shortExact z w V
          (hz.trans (hWE' z)) (hw.trans (hWE' w))) =
        E'.inclusion.hom.app (op V) (sres (holomorphicUnitSheaf X d) hw (γ w)) +
        E'.inclusion.hom.app (op V) (E.localLifts.transition E.shortExact z w V
          (hz.trans (hWE z)) (hw.trans (hWE w))) := by
      rw [← hom_add, ← hom_add, hγ z w V hz hw]
    rw [sres_add, sres_add, sres_sres, sres_sres, sres_hom, sres_hom]
    have hrw : sres E'.middle (hz.trans (hWE' z)) (E'.localLifts.lift z) +
          E'.inclusion.hom.app (op V) (sres (holomorphicUnitSheaf X d) hz (γ z)) -
        (sres E'.middle (hw.trans (hWE' w)) (E'.localLifts.lift w) +
          E'.inclusion.hom.app (op V) (sres (holomorphicUnitSheaf X d) hw (γ w))) =
        (sres E'.middle (hz.trans (hWE' z)) (E'.localLifts.lift z) -
          sres E'.middle (hw.trans (hWE' w)) (E'.localLifts.lift w)) +
        (E'.inclusion.hom.app (op V) (sres (holomorphicUnitSheaf X d) hz (γ z)) -
          E'.inclusion.hom.app (op V) (sres (holomorphicUnitSheaf X d) hw (γ w))) := by
      abel
    rw [hrw, hl]
    refine eq_of_sub_eq_zero ?_
    rw [← sub_eq_zero_of_eq hg2]
    abel

end CorrectedLifts

section FrameChange

variable (E E' : HolomorphicUnitExtension X d)
  (e : E.sectionSheafOfModules ≅ E'.sectionSheafOfModules)

set_option backward.isDefEq.respectTransparency false in
/-- A holomorphic unit regarded as a section of the holomorphic structure sheaf. -/
def unitSection {V : Opens (TopCat.of (ComplexPoint X))}
    (u : (C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯)ˣ) : (holomorphicRingSheaf X d).obj.obj (op V) := u.val

/-- Restriction of a section of the holomorphic structure sheaf. -/
abbrev ringRes {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) :
    (holomorphicRingSheaf X d).obj.obj (op V) :=
  (holomorphicRingSheaf X d).obj.map (homOfLE h).op r

/-- The common lifting neighbourhood of the two extensions at a point. -/
abbrev commonOpens (z : ComplexPoint X) : Opens (TopCat.of (ComplexPoint X)) :=
  E.localLifts.opens z ⊓ E'.localLifts.opens z

theorem mem_commonOpens (z : ComplexPoint X) : z ∈ commonOpens E E' z :=
  ⟨E.localLifts.mem_opens z, E'.localLifts.mem_opens z⟩

/-- The frame of `E` at `z`, transported along the isomorphism of section sheaves. -/
def transportedFrame (z : ComplexPoint X) :
    E'.sectionSheafOfModules.val.obj (op (commonOpens E E' z)) :=
  e.hom.val.app (op (commonOpens E E' z)) (E.frame z (commonOpens E E' z) inf_le_left)

theorem generates_transportedFrame (z : ComplexPoint X) :
    HolomorphicGenerates (transportedFrame E E' e z) :=
  (E.holomorphicGenerates_frame z (commonOpens E E' z) inf_le_left).map_iso e

theorem exists_frameChange (z : ComplexPoint X) :
    ∃ u : (holomorphicRingSheaf X d).obj.obj (op (commonOpens E E' z)), IsUnit u ∧
      u • transportedFrame E E' e z = E'.frame z (commonOpens E E' z) inf_le_right :=
  (generates_transportedFrame E E' e z).exists_isUnit_smul_eq
    (E'.holomorphicGenerates_frame z (commonOpens E E' z) inf_le_right)

/-- The chosen frame change between the transported frame of `E` and the frame of `E'`. -/
def frameChange (z : ComplexPoint X) :
    (holomorphicRingSheaf X d).obj.obj (op (commonOpens E E' z)) :=
  (exists_frameChange E E' e z).choose

theorem isUnit_frameChange (z : ComplexPoint X) : IsUnit (frameChange E E' e z) :=
  (exists_frameChange E E' e z).choose_spec.1

theorem frameChange_smul (z : ComplexPoint X) :
    frameChange E E' e z • transportedFrame E E' e z =
      E'.frame z (commonOpens E E' z) inf_le_right :=
  (exists_frameChange E E' e z).choose_spec.2

set_option backward.isDefEq.respectTransparency false in
/-- The frame changes trivialize the quotient of the two transition cocycles. -/
theorem frameChange_cocycle (z w : ComplexPoint X) (V : Opens (TopCat.of (ComplexPoint X)))
    (hz : V ≤ commonOpens E E' z) (hw : V ≤ commonOpens E E' w) :
    unitSection (E'.transitionUnit w z V (hw.trans inf_le_right) (hz.trans inf_le_right)) *
        ringRes hz (frameChange E E' e z) =
      ringRes hw (frameChange E E' e w) *
        unitSection (E.transitionUnit w z V (hw.trans inf_le_left) (hz.trans inf_le_left)) := by
  have hE : unitSection (E.transitionUnit w z V (hw.trans inf_le_left) (hz.trans inf_le_left)) •
      holRes E.sectionSheafOfModules hz (E.frame z (commonOpens E E' z) inf_le_left) =
      holRes E.sectionSheafOfModules hw (E.frame w (commonOpens E E' w) inf_le_left) := by
    rw [E.holRes_frame z inf_le_left hz, E.holRes_frame w inf_le_left hw]
    exact E.smul_frame z w V (hz.trans inf_le_left) (hw.trans inf_le_left)
  have hEg0 := smul_holRes_map_iso e hz hw _ _ _ hE
  have hEg : unitSection (E.transitionUnit w z V (hw.trans inf_le_left) (hz.trans inf_le_left)) •
      holRes E'.sectionSheafOfModules hz (transportedFrame E E' e z) =
      holRes E'.sectionSheafOfModules hw (transportedFrame E E' e w) := hEg0
  have hE' : unitSection (E'.transitionUnit w z V (hw.trans inf_le_right)
        (hz.trans inf_le_right)) •
      holRes E'.sectionSheafOfModules hz (E'.frame z (commonOpens E E' z) inf_le_right) =
      holRes E'.sectionSheafOfModules hw (E'.frame w (commonOpens E E' w) inf_le_right) := by
    rw [E'.holRes_frame z inf_le_right hz, E'.holRes_frame w inf_le_right hw]
    exact E'.smul_frame z w V (hz.trans inf_le_right) (hw.trans inf_le_right)
  have hcz : ringRes hz (frameChange E E' e z) •
      holRes E'.sectionSheafOfModules hz (transportedFrame E E' e z) =
      holRes E'.sectionSheafOfModules hz (E'.frame z (commonOpens E E' z) inf_le_right) := by
    rw [← holRes_smul, frameChange_smul]
  have hcw : ringRes hw (frameChange E E' e w) •
      holRes E'.sectionSheafOfModules hw (transportedFrame E E' e w) =
      holRes E'.sectionSheafOfModules hw (E'.frame w (commonOpens E E' w) inf_le_right) := by
    rw [← holRes_smul, frameChange_smul]
  refine (generates_transportedFrame E E' e z).smul_left_injective hz ?_
  show _ • holRes E'.sectionSheafOfModules hz (transportedFrame E E' e z) =
    _ • holRes E'.sectionSheafOfModules hz (transportedFrame E E' e z)
  rw [mul_smul, mul_smul, hcz, hE', hEg, hcw]

set_option backward.isDefEq.respectTransparency false in
/-- The frame change as an invertible holomorphic function. -/
def frameChangeUnit (z : ComplexPoint X) :
    (C^ω⟮𝓘(ℂ, Fin d → ℂ), commonOpens E E' z; ℂ⟯)ˣ := (isUnit_frameChange E E' e z).unit

set_option backward.isDefEq.respectTransparency false in
theorem unitSection_frameChangeUnit (z : ComplexPoint X) :
    unitSection (frameChangeUnit E E' e z) = frameChange E E' e z :=
  (isUnit_frameChange E E' e z).unit_spec

/-- The `0`-cochain of holomorphic units correcting the local lifts of `E'`. -/
def correctionCochain (z : ComplexPoint X) :
    (holomorphicUnitSheaf X d).obj.obj (op (commonOpens E E' z)) :=
  -(Additive.ofMul (frameChangeUnit E E' e z))

private theorem unit_algebra {gz cz gw cw A a A' a' : ℂ}
    (hcz : cz * gz = 1) (hcw : cw * gw = 1) (hA : A * a = 1) (hA' : A' * a' = 1)
    (hstar : a' * cz = cw * a) : gz * A' = gw * A := by
  have e3 : a' * A = cw * gz := by
    calc a' * A = (a' * (cz * gz)) * A := by rw [hcz]; ring
      _ = (a' * cz) * (gz * A) := by ring
      _ = (cw * a) * (gz * A) := by rw [hstar]
      _ = cw * gz * (A * a) := by ring
      _ = cw * gz := by rw [hA, mul_one]
  calc gz * A' = gz * A' * (cw * gw) := by rw [hcw, mul_one]
    _ = gw * A' * (cw * gz) := by ring
    _ = gw * A' * (a' * A) := by rw [e3]
    _ = gw * A * (A' * a') := by ring
    _ = gw * A := by rw [hA', mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The correction cochain trivializes the difference of the two transition cocycles. -/
theorem correctionCochain_spec (z w : ComplexPoint X)
    (V : Opens (TopCat.of (ComplexPoint X))) (hz : V ≤ commonOpens E E' z)
    (hw : V ≤ commonOpens E E' w) :
    sres (holomorphicUnitSheaf X d) hz (correctionCochain E E' e z) +
        E'.localLifts.transition E'.shortExact z w V (hz.trans inf_le_right)
          (hw.trans inf_le_right) =
      sres (holomorphicUnitSheaf X d) hw (correctionCochain E E' e w) +
        E.localLifts.transition E.shortExact z w V (hz.trans inf_le_left)
          (hw.trans inf_le_left) := by
  refine unitOf_injective (fun y => ?_)
  have hcz : (frameChangeUnit E E' e z).val ⟨(y : ComplexPoint X), hz y.property⟩ *
      ((frameChangeUnit E E' e z)⁻¹).val ⟨(y : ComplexPoint X), hz y.property⟩ = 1 := by
    have h : (frameChangeUnit E E' e z).val * ((frameChangeUnit E E' e z)⁻¹).val = 1 :=
      Units.mul_inv _
    exact congrArg (fun m : C^ω⟮𝓘(ℂ, Fin d → ℂ), commonOpens E E' z; ℂ⟯ =>
      m ⟨(y : ComplexPoint X), hz y.property⟩) h
  have hcw : (frameChangeUnit E E' e w).val ⟨(y : ComplexPoint X), hw y.property⟩ *
      ((frameChangeUnit E E' e w)⁻¹).val ⟨(y : ComplexPoint X), hw y.property⟩ = 1 := by
    have h : (frameChangeUnit E E' e w).val * ((frameChangeUnit E E' e w)⁻¹).val = 1 :=
      Units.mul_inv _
    exact congrArg (fun m : C^ω⟮𝓘(ℂ, Fin d → ℂ), commonOpens E E' w; ℂ⟯ =>
      m ⟨(y : ComplexPoint X), hw y.property⟩) h
  have hA : (E.transitionUnit z w V (hz.trans inf_le_left) (hw.trans inf_le_left)).val y *
      (E.transitionUnit w z V (hw.trans inf_le_left) (hz.trans inf_le_left)).val y = 1 := by
    have h : (E.transitionUnit z w V (hz.trans inf_le_left) (hw.trans inf_le_left)).val *
        (E.transitionUnit w z V (hw.trans inf_le_left) (hz.trans inf_le_left)).val = 1 := by
      rw [← Units.val_mul, E.transitionUnit_mul z w z V (hz.trans inf_le_left)
        (hw.trans inf_le_left) (hz.trans inf_le_left), E.transitionUnit_self, Units.val_one]
    exact congrArg (fun m : C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯ => m y) h
  have hA' : (E'.transitionUnit z w V (hz.trans inf_le_right) (hw.trans inf_le_right)).val y *
      (E'.transitionUnit w z V (hw.trans inf_le_right) (hz.trans inf_le_right)).val y = 1 := by
    have h : (E'.transitionUnit z w V (hz.trans inf_le_right) (hw.trans inf_le_right)).val *
        (E'.transitionUnit w z V (hw.trans inf_le_right) (hz.trans inf_le_right)).val = 1 := by
      rw [← Units.val_mul, E'.transitionUnit_mul z w z V (hz.trans inf_le_right)
        (hw.trans inf_le_right) (hz.trans inf_le_right), E'.transitionUnit_self, Units.val_one]
    exact congrArg (fun m : C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯ => m y) h
  have hco := frameChange_cocycle E E' e z w V hz hw
  rw [← unitSection_frameChangeUnit E E' e z, ← unitSection_frameChangeUnit E E' e w] at hco
  have hstar : (E'.transitionUnit w z V (hw.trans inf_le_right) (hz.trans inf_le_right)).val y *
      (frameChangeUnit E E' e z).val ⟨(y : ComplexPoint X), hz y.property⟩ =
      (frameChangeUnit E E' e w).val ⟨(y : ComplexPoint X), hw y.property⟩ *
      (E.transitionUnit w z V (hw.trans inf_le_left) (hz.trans inf_le_left)).val y :=
    congrArg (fun m : C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯ => m y) hco
  exact unit_algebra hcz hcw hA hA' hstar

include e in
/-- Isomorphic section sheaves produce a system of corrected lifts. -/
theorem nonempty_correctedLifts : Nonempty (CorrectedLifts E E') :=
  ⟨CorrectedLifts.ofUnitCochain E E' (commonOpens E E') (mem_commonOpens E E')
    (fun _ => inf_le_left) (fun _ => inf_le_right) (correctionCochain E E' e)
    (correctionCochain_spec E E' e)⟩

end FrameChange


end AlgebraicGeometry.ComplexPoint
