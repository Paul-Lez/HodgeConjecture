/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSegre
public import Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff

/-!
# The analytic self-product underlying the explicit elliptic surface

The scheme `surface` is the fiber product of the explicit cubic with itself over
`Spec ℂ`.  A complex point of the fiber product is therefore exactly a pair of
complex points of the cubic.  The projection map is continuous by functoriality of
analytification.  Since the source is compact and the product target is Hausdorff,
the resulting continuous bijection is a homeomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open Point

/-- The first projection of the explicit surface, as a morphism over `Spec ℂ`. -/
def surfaceVarietyFst : surfaceVariety ⟶ curveVariety :=
  Over.homMk (pullback.fst curveToBase curveToBase) rfl

/-- The second projection of the explicit surface, as a morphism over `Spec ℂ`. -/
def surfaceVarietySnd : surfaceVariety ⟶ curveVariety :=
  Over.homMk (pullback.snd curveToBase curveToBase) pullback.condition.symm

/-- A complex point of the explicit surface gives its two elliptic-curve coordinates. -/
def surfaceComplexPointToPair :
    ComplexPoint surfaceVariety →
      ComplexPoint curveVariety × ComplexPoint curveVariety :=
  fun z => (Point.map surfaceVarietyFst z, Point.map surfaceVarietySnd z)

/-- The two curve points of a pair have the same structure map to `Spec ℂ`. -/
theorem curveComplexPointPair_base
    (z : ComplexPoint curveVariety × ComplexPoint curveVariety) :
    z.1.left ≫ curveToBase = z.2.left ≫ curveToBase := by
  have h₁ := Over.w z.1
  have h₂ := Over.w z.2
  rw [show curveVariety.hom = curveToBase from rfl] at h₁ h₂
  exact h₁.trans h₂.symm

/-- A pair of complex points of the cubic lifts through the scheme-theoretic fiber product. -/
def curveComplexPointPairToSurface
    (z : ComplexPoint curveVariety × ComplexPoint curveVariety) :
    ComplexPoint surfaceVariety :=
  Over.homMk
    (pullback.lift z.1.left z.2.left
      (curveComplexPointPair_base z))
    (by
      have hz : z.1.left ≫ curveToBase =
          (Over.mk (𝟙 (Spec (CommRingCat.of ℂ)))).hom := by
        have h := Over.w z.1
        rw [show curveVariety.hom = curveToBase from rfl] at h
        exact h
      rw [show surfaceVariety.hom =
        pullback.fst curveToBase curveToBase ≫ curveToBase from rfl]
      exact (pullback.lift_fst_assoc z.1.left z.2.left
        (curveComplexPointPair_base z) curveToBase).trans hz)

@[simp]
theorem curveComplexPointPairToSurface_fst
    (z : ComplexPoint curveVariety × ComplexPoint curveVariety) :
    Point.map surfaceVarietyFst (curveComplexPointPairToSurface z) = z.1 := by
  apply Over.OverMorphism.ext
  change (curveComplexPointPairToSurface z).left ≫ surfaceVarietyFst.left = z.1.left
  rw [show surfaceVarietyFst.left = pullback.fst curveToBase curveToBase from rfl]
  change pullback.lift z.1.left z.2.left (curveComplexPointPair_base z) ≫
    pullback.fst curveToBase curveToBase = z.1.left
  exact pullback.lift_fst _ _ _

@[simp]
theorem curveComplexPointPairToSurface_snd
    (z : ComplexPoint curveVariety × ComplexPoint curveVariety) :
    Point.map surfaceVarietySnd (curveComplexPointPairToSurface z) = z.2 := by
  apply Over.OverMorphism.ext
  change (curveComplexPointPairToSurface z).left ≫ surfaceVarietySnd.left = z.2.left
  rw [show surfaceVarietySnd.left = pullback.snd curveToBase curveToBase from rfl]
  change pullback.lift z.1.left z.2.left (curveComplexPointPair_base z) ≫
    pullback.snd curveToBase curveToBase = z.2.left
  exact pullback.lift_snd _ _ _

@[simp]
theorem surfaceComplexPointToPair_curveComplexPointPairToSurface
    (z : ComplexPoint curveVariety × ComplexPoint curveVariety) :
    surfaceComplexPointToPair (curveComplexPointPairToSurface z) = z := by
  ext <;> simp [surfaceComplexPointToPair]

@[simp]
theorem curveComplexPointPairToSurface_surfaceComplexPointToPair
    (z : ComplexPoint surfaceVariety) :
    curveComplexPointPairToSurface (surfaceComplexPointToPair z) = z := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h := congrArg Over.Hom.left
      (curveComplexPointPairToSurface_fst (surfaceComplexPointToPair z))
    change (curveComplexPointPairToSurface (surfaceComplexPointToPair z)).left ≫
      surfaceVarietyFst.left = z.left ≫ surfaceVarietyFst.left at h
    rw [show surfaceVarietyFst.left = pullback.fst curveToBase curveToBase from rfl] at h
    exact h
  · have h := congrArg Over.Hom.left
      (curveComplexPointPairToSurface_snd (surfaceComplexPointToPair z))
    change (curveComplexPointPairToSurface (surfaceComplexPointToPair z)).left ≫
      surfaceVarietySnd.left = z.left ≫ surfaceVarietySnd.left at h
    rw [show surfaceVarietySnd.left = pullback.snd curveToBase curveToBase from rfl] at h
    exact h

/-- The set-level universal property of the fiber product on complex points. -/
def surfaceComplexPointEquiv :
    ComplexPoint surfaceVariety ≃
      ComplexPoint curveVariety × ComplexPoint curveVariety where
  toFun := surfaceComplexPointToPair
  invFun := curveComplexPointPairToSurface
  left_inv := curveComplexPointPairToSurface_surfaceComplexPointToPair
  right_inv := surfaceComplexPointToPair_curveComplexPointPairToSurface

/-- The projection map from the surface analytification to the product analytification is
continuous. -/
theorem continuous_surfaceComplexPointToPair :
    Continuous surfaceComplexPointToPair :=
  (Point.continuous_map surfaceVarietyFst).prodMk
    (Point.continuous_map surfaceVarietySnd)

/-- The analytification of the explicit scheme-theoretic self-product is homeomorphic to the
topological self-product of the elliptic curve analytification. -/
def surfaceComplexPointHomeomorph :
    ComplexPoint surfaceVariety ≃ₜ
      ComplexPoint curveVariety × ComplexPoint curveVariety := by
  let e := surfaceComplexPointEquiv
  let h : IsHomeomorph e :=
    (isHomeomorph_iff_continuous_bijective).2
      ⟨continuous_surfaceComplexPointToPair, e.bijective⟩
  exact
    { toEquiv := e
      continuous_toFun := h.continuous
      continuous_invFun := ((Equiv.isHomeomorph_iff e).mp h).2 }

@[simp]
theorem surfaceComplexPointHomeomorph_apply (z : ComplexPoint surfaceVariety) :
    surfaceComplexPointHomeomorph z =
      (Point.map surfaceVarietyFst z, Point.map surfaceVarietySnd z) :=
  rfl

@[simp]
theorem surfaceComplexPointHomeomorph_symm_apply
    (z : ComplexPoint curveVariety × ComplexPoint curveVariety) :
    surfaceComplexPointHomeomorph.symm z = curveComplexPointPairToSurface z :=
  rfl

end AlgebraicGeometry.ExplicitEllipticCandidate
