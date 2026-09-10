/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLineBundleOfExtension
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The sheaf of holomorphic sections of a line bundle

Holomorphicity of sections is a local condition on the base. Extending the fiber coordinates
by zero lets us express this condition using ordinary manifold differentiability at points
of an open subset; the values outside that subset play no role.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Bundle Filter
open scoped Manifold ContDiff Topology

namespace AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance holomorphicLineBundleSectionsTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension X d)

/-- Fiber coordinates extended by zero outside an open set. -/
def extendSection (U : Opens (TopCat.of (ComplexPoint X))) (f : U → ℂ)
    (x : ComplexPoint X) : E.lineBundleCore.Fiber x := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 0

/-- A partial section represented as a total-space map on the base. -/
def extendedSectionMap (U : Opens (TopCat.of (ComplexPoint X))) (f : U → ℂ) :
    ComplexPoint X → E.lineBundleCore.TotalSpace :=
  fun x => TotalSpace.mk' ℂ x (E.extendSection U f x)

/-- The extended section agrees with the given fiber coordinates on its domain. -/
theorem extendSection_of_mem (U : Opens (TopCat.of (ComplexPoint X))) (f : U → ℂ)
    (x : ComplexPoint X) (hx : x ∈ U) : E.extendSection U f x = f ⟨x, hx⟩ :=
  dif_pos hx

/-- The extended section is zero outside its domain. -/
theorem extendSection_of_notMem (U : Opens (TopCat.of (ComplexPoint X))) (f : U → ℂ)
    (x : ComplexPoint X) (hx : x ∉ U) : E.extendSection U f x = 0 :=
  dif_neg hx

/-- On the domain, the total-space map has the prescribed fiber coordinate. -/
theorem extendedSectionMap_of_mem (U : Opens (TopCat.of (ComplexPoint X))) (f : U → ℂ)
    (x : ComplexPoint X) (hx : x ∈ U) : E.extendedSectionMap U f x =
      TotalSpace.mk' ℂ x (f ⟨x, hx⟩ : E.lineBundleCore.Fiber x) := by
  unfold extendedSectionMap
  rw [E.extendSection_of_mem U f x hx]

/-- Holomorphicity is a local predicate on fiber coordinates. -/
def holomorphicSectionPredicate :
    TopCat.LocalPredicate (fun _ : TopCat.of (ComplexPoint X) => ℂ) where
  pred {U} f := ∀ x : U, ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
    (𝓘(ℂ, Fin d → ℂ).prod 𝓘(ℂ)) ω (E.extendedSectionMap U f) x
  res {U V} i f hf x := by
    apply (hf ⟨x, i.le x.property⟩).congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    rw [E.extendedSectionMap_of_mem _ _ y hy, E.extendedSectionMap_of_mem _ _ y (i.le hy)]
    rfl
  locality {U} f hf x := by
    obtain ⟨V, hx, i, hi⟩ := hf x
    apply (hi ⟨x, hx⟩).congr_of_eventuallyEq
    filter_upwards [V.isOpen.mem_nhds hx] with y hy
    rw [E.extendedSectionMap_of_mem _ _ y (i.le hy), E.extendedSectionMap_of_mem _ _ y hy]
    rfl

/-- Holomorphic sections form an additive subgroup of all fiber-coordinate functions. -/
def sectionAddSubgroup (U : Opens (TopCat.of (ComplexPoint X))) : AddSubgroup (U → ℂ) where
  carrier := E.holomorphicSectionPredicate.pred
  zero_mem' := by
    intro x
    have h : E.extendedSectionMap U 0 = zeroSection ℂ E.lineBundleCore.Fiber := by
      funext y
      unfold extendedSectionMap
      by_cases hy : y ∈ U
      · rw [E.extendSection_of_mem U 0 y hy]
        rfl
      · rw [E.extendSection_of_notMem U 0 y hy]
        rfl
    rw [h]
    exact contMDiffAt_zeroSection ℂ E.lineBundleCore.Fiber
  add_mem' {f g} hf hg := by
    intro x
    have h : E.extendSection U (f + g) = E.extendSection U f + E.extendSection U g := by
      funext y
      change E.extendSection U (f + g) y = E.extendSection U f y + E.extendSection U g y
      by_cases hy : y ∈ U
      · rw [E.extendSection_of_mem U (f + g) y hy, E.extendSection_of_mem U f y hy,
          E.extendSection_of_mem U g y hy]
        rfl
      · rw [E.extendSection_of_notMem U (f + g) y hy, E.extendSection_of_notMem U f y hy,
          E.extendSection_of_notMem U g y hy, add_zero]
    change ContMDiffAt _ _ _ (fun y => TotalSpace.mk' ℂ y (E.extendSection U (f + g) y)) _
    rw [h]
    exact (hf x).add_section (hg x)
  neg_mem' {f} hf := by
    intro x
    have h : E.extendSection U (-f) = -E.extendSection U f := by
      funext y
      change E.extendSection U (-f) y = -E.extendSection U f y
      by_cases hy : y ∈ U
      · rw [E.extendSection_of_mem U (-f) y hy, E.extendSection_of_mem U f y hy]
        rfl
      · rw [E.extendSection_of_notMem U (-f) y hy, E.extendSection_of_notMem U f y hy, neg_zero]
    change ContMDiffAt _ _ _ (fun y => TotalSpace.mk' ℂ y (E.extendSection U (-f) y)) _
    rw [h]
    exact (hf x).neg_section

/-- The abelian group of holomorphic sections on an open set. -/
abbrev HolomorphicSections (U : Opens (TopCat.of (ComplexPoint X))) :=
  ↥(E.sectionAddSubgroup U)

/-- Restriction of holomorphic sections is additive. -/
def sectionRestriction {U V : Opens (TopCat.of (ComplexPoint X))} (i : U ⟶ V) :
    E.HolomorphicSections V →+ E.HolomorphicSections U where
  toFun f := ⟨fun x => f.val ⟨x, i.le x.property⟩,
    E.holomorphicSectionPredicate.res i f.val f.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The presheaf of holomorphic sections of the constructed line bundle. -/
def sectionPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) where
  obj U := AddCommGrpCat.of (E.HolomorphicSections (unop U))
  map i := AddCommGrpCat.ofHom (E.sectionRestriction i.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Holomorphic sections satisfy the sheaf condition. -/
def sectionSheaf : AnalyticAdditiveSheaf X where
  obj := E.sectionPresheaf
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat)]
    exact (TopCat.subsheafToTypes E.holomorphicSectionPredicate).property

end AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension
