/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.PointJetSectionGerm
public import Other.AlgebraicGeometry.CartierLocalDerivative
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothClosedLift

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Order
open IsLocalRing
open scoped Manifold

namespace AlgebraicGeometry.ComplexPoint.Affine

open AlgebraicGeometry.ComplexPoint Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/- The stalk comparison for a section restricted along an open immersion. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem openInclusion_stalk_germ_eq
    (U : X.left.Opens) (W : X.left.Opens)
    (y : ComplexPoint (openScheme X U))
    (hyW : U.ι y.underlying ∈ W) (s : Γ(X.left, W)) :
    (U.stalkIso y.underlying).commRingCatIsoToRingEquiv
        (U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ W) y.underlying (by exact hyW)
          (U.ι.app W s)) =
      X.left.presheaf.germ W (U.ι y.underlying) hyW s := by
  dsimp only
  apply (U.stalkIso y.underlying).commRingCatIsoToRingEquiv.symm.injective
  rw [RingEquiv.symm_apply_apply]
  change _ = (U.stalkIso y.underlying).inv.hom
    (X.left.presheaf.germ W (U.ι y.underlying) hyW s)
  rw [Scheme.Opens.stalkIso_inv]
  exact (Scheme.Hom.germ_stalkMap_apply U.ι W y.underlying hyW s).symm

/-- A first-order germ detected on an ambient scheme remains detected after passing to an open
subscheme. The equality `hg` is the canonical stalk comparison for the restricted section. -/
theorem regularPointJet_ne_zero_of_open_restriction_of_germ
    [SmoothOfRelativeDimension d X.hom]
    (U : X.left.Opens) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (y : ComplexPoint (openScheme X U))
    (V : U.toScheme.Opens) (hyV : y.underlying ∈ V)
    (t : Γ(U.toScheme, V)) (W : X.left.Opens)
    (hyW : U.ι y.underlying ∈ W)
    (s : Γ(X.left, W))
    (hg :
      ((U.stalkIso y.underlying).commRingCatIsoToRingEquiv)
          (U.toScheme.presheaf.germ V y.underlying hyV t) =
        X.left.presheaf.germ W (U.ι y.underlying) hyW s)
    (hs : X.left.presheaf.germ W (U.ι y.underlying) hyW s ∈
      maximalIdeal (X.left.presheaf.stalk (U.ι y.underlying)))
    (hs2 : X.left.presheaf.germ W (U.ι y.underlying) hyW s ∉
      (maximalIdeal (X.left.presheaf.stalk (U.ι y.underlying))) ^ 2) :
    regularPointJet (openScheme X U) d V y hyV t ≠ 0 := by
  let e : (U.toScheme.presheaf.stalk y.underlying) ≃+*
      X.left.presheaf.stalk (U.ι y.underlying) :=
    (U.stalkIso y.underlying).commRingCatIsoToRingEquiv
  let g := U.toScheme.presheaf.germ V y.underlying hyV t
  have hgs := hs
  rw [← hg] at hgs
  change e g ∈ maximalIdeal _ at hgs
  have ht : U.toScheme.presheaf.germ V y.underlying hyV t ∈ maximalIdeal
      (U.toScheme.presheaf.stalk y.underlying) := by
    have h := (RingEquiv.mem_maximalIdeal_pow_iff e g 1).mpr (by
      simpa only [pow_one] using hgs)
    simpa only [g, pow_one] using h
  have ht2 : U.toScheme.presheaf.germ V y.underlying hyV t ∉
      (maximalIdeal (U.toScheme.presheaf.stalk y.underlying)) ^ 2 := by
    intro h
    have h' := (RingEquiv.mem_maximalIdeal_pow_iff e g 2).mp h
    apply hs2
    rw [← hg]
    change e g ∈ (maximalIdeal _) ^ 2 at h'
    exact h'
  exact regularPointJet_ne_zero_of_germ_mem_maximalIdeal_of_not_mem_square
    (openScheme X U) d V y hyV t ht ht2

end AlgebraicGeometry.ComplexPoint.Affine

namespace AlgebraicGeometry.ComplexPoint.Affine

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

/-- The local equation of a codimension-one component has nonzero ambient first jet on every
smooth point of the component lying in the generic principal shrink. -/
theorem regularPointJet_ne_zero_of_component_equation
    (c : Scheme.CartierData X.left) (x : X.left) {i : c.ι} (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (f : c.LocalForm i x)
    (hx : coheight x = 1) (s : Γ(X.left, f.opens))
    (hs : s ∉ (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal)
    (hEq :
      (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal.map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)) =
        (Ideal.span {f.equation}).map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)))
    (U : X.left.Opens) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (zM : ComplexPoint (openScheme X U))
    (zC : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
    (hzC : zC.underlying ∈ (cycleComponentι X.left x ≫ X.hom).smoothLocus)
    (hyC : cycleComponentι X.left x zC.underlying ∈ f.opens)
    (hysC : cycleComponentι X.left x zC.underlying ∈ X.left.basicOpen s)
    (hmap : Point.map (openInclusion X U) zM =
      Point.map (Over.homMk (cycleComponentι X.left x) rfl) zC)
    (V : U.toScheme.Opens) (hzV : zM.underlying ∈ V)
    (t : Γ(U.toScheme, V)) (hyU : U.ι zM.underlying ∈ f.opens)
    (hgt :
      (U.stalkIso zM.underlying).commRingCatIsoToRingEquiv
          (U.toScheme.presheaf.germ V zM.underlying hzV t) =
        X.left.presheaf.germ f.opens (U.ι zM.underlying) hyU f.equation) :
    regularPointJet (openScheme X U) d V zM hzV t ≠ 0 := by
  let iC : Over.mk (cycleComponentι X.left x ≫ X.hom) ⟶ X :=
    Over.homMk (cycleComponentι X.left x) rfl
  let zX := Point.map (openInclusion X U) zM
  have hpoint : U.ι zM.underlying = cycleComponentι X.left x zC.underlying := by
    have h := congrArg Point.underlying hmap
    simpa [iC] using h
  have hyX : U.ι zM.underlying ∈ f.opens := hyU
  have hnsC := Scheme.CartierData.LocalForm.germ_equation_not_mem_square_of_component_of_away
    c x d f hx s hs hEq zC hzC hyC hysC
  have hnsX : X.left.presheaf.germ f.opens (U.ι zM.underlying) hyX f.equation ∉
      (maximalIdeal (X.left.presheaf.stalk (U.ι zM.underlying))) ^ 2 := by
    let e : Inseparable (U.ι zM.underlying)
        (cycleComponentι X.left x zC.underlying) := .of_eq hpoint
    let j := (X.left.presheaf.stalkCongr e).commRingCatIsoToRingEquiv
    let gU := X.left.presheaf.germ f.opens (U.ι zM.underlying) hyX f.equation
    let gC := X.left.presheaf.germ f.opens
      (cycleComponentι X.left x zC.underlying) hyC f.equation
    have hmapg : j gU = gC := by
      change ((X.left.presheaf.stalkCongr e).hom.hom gU) = gC
      dsimp [e, TopCat.Presheaf.stalkCongr]
      have hsp := TopCat.Presheaf.germ_stalkSpecializes
        X.left.presheaf hyX (x := cycleComponentι X.left x zC.underlying) e.ge
      have hsp' := congrArg (fun k => k.hom f.equation) hsp
      simpa only [ConcreteCategory.comp_apply, gU, gC] using hsp'
    intro h
    apply hnsC
    have h' := (RingEquiv.mem_maximalIdeal_pow_iff j gU 2).mp h
    rw [hmapg] at h'
    exact h'
  have hzX : zX ∈ Point.overOpen f.opens := by
    change U.ι zM.underlying ∈ f.opens
    exact hyX
  have hzX' : zX.underlying ∈ f.opens := by
    change U.ι zM.underlying ∈ f.opens
    exact hyX
  have hcl : zX.underlying ∈ closure ({x} : Set X.left) := by
    change U.ι zM.underlying ∈ closure ({x} : Set X.left)
    rw [hpoint]
    exact range_cycleComponentMap_subset X x ⟨zC, rfl⟩
  have hzero : Point.evaluate f.opens f.equation zX = 0 := by
    have hnot : ¬ Point.evaluate f.opens f.equation zX ≠ 0 := by
      intro hne
      exact (f.notMem_basicOpen _ hcl)
        ((Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
          f.equation zX hzX).mpr hne)
    exact not_not.mp hnot
  let gX := X.left.presheaf.germ f.opens zX.underlying hzX' f.equation
  have hgX : gX ∈ maximalIdeal (X.left.presheaf.stalk zX.underlying) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hunitval : IsUnit (zX.stalkHom gX) := hunit.map zX.stalkHom.hom
    have hne : Point.evaluate f.opens f.equation zX ≠ 0 := by
      rw [Point.evaluate, dif_pos hzX']
      exact isUnit_iff_ne_zero.mp hunitval
    exact hne hzero
  have hgX' : X.left.presheaf.germ f.opens (U.ι zM.underlying) hyX f.equation ∈
      maximalIdeal (X.left.presheaf.stalk (U.ι zM.underlying)) := by
    change gX ∈ maximalIdeal (X.left.presheaf.stalk zX.underlying) at hgX
    exact hgX
  exact regularPointJet_ne_zero_of_open_restriction_of_germ X d U zM V hzV t
    f.opens hyX f.equation hgt hgX' hnsX

/-- The preceding component calculation in the chart's derivative form. -/
theorem fderiv_ne_zero_of_component_equation
    (c : Scheme.CartierData X.left) (x : X.left) {i : c.ι} (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (f : c.LocalForm i x)
    (hx : coheight x = 1) (s : Γ(X.left, f.opens))
    (hs : s ∉ (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal)
    (hEq :
      (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal.map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)) =
        (Ideal.span {f.equation}).map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)))
    (U : X.left.Opens) [SmoothOfRelativeDimension d (openScheme X U).hom]
    (zM : ComplexPoint (openScheme X U))
    (zC : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
    (hzC : zC.underlying ∈ (cycleComponentι X.left x ≫ X.hom).smoothLocus)
    (hyC : cycleComponentι X.left x zC.underlying ∈ f.opens)
    (hysC : cycleComponentι X.left x zC.underlying ∈ X.left.basicOpen s)
    (hmap : Point.map (openInclusion X U) zM =
      Point.map (Over.homMk (cycleComponentι X.left x) rfl) zC)
    (hyU : U.ι zM.underlying ∈ f.opens) :
    fderiv ℂ
        (fun w ↦ Point.evaluate (U.ι ⁻¹ᵁ f.opens)
          (U.ι.app f.opens f.equation)
          ((localChart (openScheme X U) d zM).symm w))
        (localChart (openScheme X U) d zM zM) ≠ 0 := by
  have hjet := regularPointJet_ne_zero_of_component_equation X c x d f hx s hs hEq U zM zC
    hzC hyC hysC hmap (U.ι ⁻¹ᵁ f.opens) (by exact hyU)
    (U.ι.app f.opens f.equation) hyU
    (openInclusion_stalk_germ_eq X U f.opens zM hyU f.equation)
  simpa only [regularPointJet] using hjet

end AlgebraicGeometry.ComplexPoint.Affine
