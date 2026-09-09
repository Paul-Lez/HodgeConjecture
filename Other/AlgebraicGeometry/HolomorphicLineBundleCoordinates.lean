/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLineBundleModule

/-!
# Local coordinates for holomorphic line-bundle sections

On an open subset of a trivializing neighborhood, holomorphic sections are linearly
equivalent to holomorphic functions. Both directions use the actual bundle trivialization.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Bundle Filter
open scoped Manifold ContDiff Topology

namespace AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension

variable {X : Scheme} {s : X ⟶ Spec ↧ℂ} {d : ℕ} [SmoothOfRelativeDimension d s]

local instance holomorphicLineBundleCoordinatesTopology : TopologicalSpace (ComplexPoint X s) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension s d) (i : ComplexPoint X s)
  (U : Opens (TopCat.of (ComplexPoint X s))) (hU : U ≤ E.localLifts.opens i)

local instance holomorphicLineBundleCoordinates_memAtlas :
    MemTrivializationAtlas (E.lineBundleCore.localTriv i) where
  out := ⟨i, rfl⟩

/-- Express a holomorphic section as a holomorphic function in one local frame. -/
def localCoordinateFunction (f : E.HolomorphicSections U) : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯ :=
  ⟨fun x => (E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x (hU x.property) (f.val x),
    by
      have hfun : (fun x : U => (E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x
          (hU x.property) (f.val x)) = fun x : U =>
          ((E.lineBundleCore.localTriv i) (E.extendedSectionMap U f.val x)).2 := by
        funext x
        rw [E.extendedSectionMap_of_mem U f.val x x.property]
        rfl
      rw [hfun]
      intro x
      apply (contMDiffAt_subtype_iff (U := U) (x := x)
        (f := fun y => ((E.lineBundleCore.localTriv i) (E.extendedSectionMap U f.val y)).2)).mpr
      exact ((E.lineBundleCore.localTriv i).contMDiffAt_section_iff
        (hU x.property)).mp (f.property x)⟩

/-- Form a holomorphic section from its holomorphic coordinate in one local frame. -/
def sectionOfLocalCoordinate (a : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) : E.HolomorphicSections U :=
  ⟨fun x => ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x
      (hU x.property)).symm (a x), by
    intro x
    apply ((E.lineBundleCore.localTriv i).contMDiffAt_section_iff (hU x.property)).mpr
    apply (E.contMDiffAt_extendSection_scalar U a x).congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    change ((E.lineBundleCore.localTriv i) (E.extendedSectionMap U _ y)).2 =
      (E.extendSection U a y : ℂ)
    erw [E.extendedSectionMap_of_mem U _ y hy, E.extendSection_of_mem U a y hy]
    exact ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ y
      (hU hy)).apply_symm_apply (a ⟨y, hy⟩)⟩

/-- Local trivialization identifies the section module with the rank-one free function module. -/
def localCoordinateEquiv : E.HolomorphicSections U ≃ₗ[C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯]
    C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯ where
  toFun := E.localCoordinateFunction i U hU
  invFun := E.sectionOfLocalCoordinate i U hU
  left_inv f := by
    apply Subtype.ext
    funext x
    exact ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x
      (hU x.property)).symm_apply_apply (f.val x)
  right_inv a := by
    apply Subtype.ext
    funext x
    exact ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x
      (hU x.property)).apply_symm_apply (a x)
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact map_add ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x
      (hU x.property)) (f.val x) (g.val x)
  map_smul' a f := by
    apply Subtype.ext
    funext x
    exact map_smul ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x
      (hU x.property)) (a x) (f.val x)

end AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension
