/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.CartierLocalComponentKernel
public import Other.AlgebraicGeometry.Cycle.Component.RegularImmersion
public import Other.RingTheory.RegularLocalEquation

/-!
# First-order local equation on a smooth component
-/

@[expose] public noncomputable section

open CategoryTheory Topology Order

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

namespace Scheme.CartierData.LocalForm

variable {X} (c : Scheme.CartierData X.left) {i : c.ι} (x : X.left) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- A germ generating the component stalk ideal has nonzero ambient cotangent class at a smooth
component point. -/
theorem germ_equation_not_mem_square_of_component
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : c.LocalForm i x) (hx : coheight x = 1)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
    (hz : z.underlying ∈ (cycleComponentι X.left x ≫ X.hom).smoothLocus)
    (hy : cycleComponentι X.left x z.underlying ∈ f.opens)
    (hgen : Ideal.span ({X.left.presheaf.germ f.opens (cycleComponentι X.left x z.underlying)
        hy f.equation} : Set
          (X.left.presheaf.stalk (cycleComponentι X.left x z.underlying))) =
      RingHom.ker ((cycleComponentι X.left x).stalkMap z.underlying).hom) :
    X.left.presheaf.germ f.opens (cycleComponentι X.left x z.underlying)
      hy f.equation ∉
        (IsLocalRing.maximalIdeal
          (X.left.presheaf.stalk (cycleComponentι X.left x z.underlying))) ^ 2 := by
  let R := X.left.presheaf.stalk (cycleComponentι X.left x z.underlying)
  let a : R := X.left.presheaf.germ f.opens (cycleComponentι X.left x z.underlying)
    hy f.equation
  let I : Ideal R := Ideal.span ({a} : Set R)
  have hR : IsRegularLocalRing R :=
    cycleComponent_ambient_stalk_isRegularLocalRing (d := d) X x z.underlying
  have hI : I = RingHom.ker ((cycleComponentι X.left x).stalkMap z.underlying).hom := by
    simpa [I, a, R] using hgen
  have hQ : IsRegularLocalRing
      (R ⧸ I) := by
    rw [hI]
    simpa [R] using
      (cycleComponent_stalkMap_quotient_isRegularLocalRing_of_mem_smoothLocus X x z.underlying hz)
  have hdim : ringKrullDim (R ⧸ I) + 1 = ringKrullDim R := by
    rw [hI,
      ringKrullDim_cycleComponent_stalkMap_quotient
        (d := d) (p := 1) X x z hx,
      ringKrullDim_cycleComponent_ambient_stalk (d := d) X x z]
    have hd : 1 ≤ d := cycleComponent_codimension_le X x hx
    exact_mod_cast (Nat.sub_add_cancel hd)
  have ha : a ∉ (IsLocalRing.maximalIdeal R) ^ 2 :=
    Ideal.generator_not_mem_square_of_regular_quotient a hQ hdim
  exact ha

/-- The first-order equation statement after the generic principal shrink. -/
theorem germ_equation_not_mem_square_of_component_of_away
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : c.LocalForm i x) (hx : coheight x = 1)
    (s : Γ(X.left, f.opens))
    (hs : s ∉ (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal)
    (hEq :
      (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal.map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)) =
        (Ideal.span {f.equation}).map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)))
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))
    (hz : z.underlying ∈ (cycleComponentι X.left x ≫ X.hom).smoothLocus)
    (hy : cycleComponentι X.left x z.underlying ∈ f.opens)
    (hys : cycleComponentι X.left x z.underlying ∈ X.left.basicOpen s) :
    X.left.presheaf.germ f.opens (cycleComponentι X.left x z.underlying)
        hy f.equation ∉
      (IsLocalRing.maximalIdeal
        (X.left.presheaf.stalk (cycleComponentι X.left x z.underlying))) ^ 2 := by
  have hgen := span_germ_equation_eq_component_stalkMap_ker_of_away
    c x f s hs hEq z.underlying hy hys
  exact germ_equation_not_mem_square_of_component
    (c := c) (x := x) d f hx z hz hy hgen

end Scheme.CartierData.LocalForm

end AlgebraicGeometry
