/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticHolomorphicDifferentials
public import Other.AlgebraicGeometry.RegularSectionPullback

/-!
# Pulling the elliptic differential back to its self-product

These maps use the actual section pullbacks of morphisms over the complex base.
The compatibility of the two elliptic chart formulas is preserved by pullback.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] regularSectionAlgebra

local instance surfacePullbackSectionAlgebra (V : surface.Opens) :
    Algebra ℂ Γ(surface, V) := regularSectionAlgebra (Over.mk surfaceToBase) V

/-- Restriction of regular functions on the actual product surface. -/
def surfaceSectionRestriction {U V : surface.Opens} (h : V ≤ U) :
    Γ(surface, U) →ₐ[ℂ] Γ(surface, V) :=
  regularSectionRestriction (Over.mk surfaceToBase) h

/-- Restriction on the product surface's Kähler differential modules. -/
def surfaceDifferentialRestriction {U V : surface.Opens} (h : V ≤ U) :
    KaehlerDifferential ℂ Γ(surface, U) →ₗ[ℂ] KaehlerDifferential ℂ Γ(surface, V) :=
  let := (surfaceSectionRestriction h).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(surface, U) Γ(surface, V) :=
    IsScalarTower.of_algebraMap_eq' (surfaceSectionRestriction h).comp_algebraMap.symm
  (KaehlerDifferential.map ℂ ℂ Γ(surface, U) Γ(surface, V)).restrictScalars ℂ

@[simp] theorem surfaceDifferentialRestriction_D {U V : surface.Opens} (h : V ≤ U)
    (b : Γ(surface, U)) :
    surfaceDifferentialRestriction h (KaehlerDifferential.D ℂ Γ(surface, U) b) =
      KaehlerDifferential.D ℂ Γ(surface, V) (surfaceSectionRestriction h b) := by
  simp only [surfaceDifferentialRestriction, LinearMap.restrictScalars_apply,
    KaehlerDifferential.map_D]
  rfl

@[simp] theorem surfaceDifferentialRestriction_smul {U V : surface.Opens} (h : V ≤ U)
    (a : Γ(surface, U)) (w : KaehlerDifferential ℂ Γ(surface, U)) :
    surfaceDifferentialRestriction h (a • w) =
      surfaceSectionRestriction h a • surfaceDifferentialRestriction h w := by
  let := (surfaceSectionRestriction h).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(surface, U) Γ(surface, V) :=
    IsScalarTower.of_algebraMap_eq' (surfaceSectionRestriction h).comp_algebraMap.symm
  exact (KaehlerDifferential.map ℂ ℂ Γ(surface, U) Γ(surface, V)).map_smul a w

variable (f : surface ⟶ curve) (hbase : f ≫ curveToBase = surfaceToBase)

/-- Actual pullback of sections, with the complex scalar structures on both schemes. -/
def surfaceSectionPullback (U : curve.Opens) (V : surface.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    Γ(curve, U) →ₐ[ℂ] Γ(surface, V) :=
  regularSectionPullback
    (Over.homMk f hbase : Over.mk surfaceToBase ⟶ Over.mk curveToBase) U V h

/-- The induced pullback on the actual Kähler differential modules. -/
def surfaceDifferentialPullback (U : curve.Opens) (V : surface.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    KaehlerDifferential ℂ Γ(curve, U) →ₗ[ℂ] KaehlerDifferential ℂ Γ(surface, V) :=
  let := (surfaceSectionPullback f hbase U V h).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(curve, U) Γ(surface, V) :=
    IsScalarTower.of_algebraMap_eq' (surfaceSectionPullback f hbase U V h).comp_algebraMap.symm
  (KaehlerDifferential.map ℂ ℂ Γ(curve, U) Γ(surface, V)).restrictScalars ℂ

@[simp] theorem surfaceDifferentialPullback_smul_D
    (U : curve.Opens) (V : surface.Opens) (h : V ≤ f ⁻¹ᵁ U) (a b : Γ(curve, U)) :
    surfaceDifferentialPullback f hbase U V h (a • KaehlerDifferential.D ℂ Γ(curve, U) b) =
      surfaceSectionPullback f hbase U V h a •
        KaehlerDifferential.D ℂ Γ(surface, V) (surfaceSectionPullback f hbase U V h b) := by
  let := (surfaceSectionPullback f hbase U V h).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(curve, U) Γ(surface, V) :=
    IsScalarTower.of_algebraMap_eq' (surfaceSectionPullback f hbase U V h).comp_algebraMap.symm
  change (KaehlerDifferential.map ℂ ℂ Γ(curve, U) Γ(surface, V))
    (a • KaehlerDifferential.D ℂ Γ(curve, U) b) = _
  rw [map_smul, KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_smul Γ(surface, V) a]
  rfl

/-- Pullback of a restricted curve differential is the pullback of that differential. -/
theorem surfaceDifferentialPullback_restrict_curve {U W : curve.Opens} (hWU : W ≤ U)
    (V : surface.Opens) (h : V ≤ f ⁻¹ᵁ W) (w : KaehlerDifferential ℂ Γ(curve, U)) :
    surfaceDifferentialPullback f hbase W V h (curveDifferentialRestriction hWU w) =
      surfaceDifferentialPullback f hbase U V
        (h.trans ((Opens.map f.base).map (homOfLE hWU)).le) w := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ Γ(curve, U) w
  induction v using Finsupp.induction with
  | zero => simp
  | single_add b a v hb ha ih =>
    simp only [map_add, Finsupp.linearCombination_single, ih]
    congr 1
    rw [curveDifferentialRestriction_smul, curveDifferentialRestriction_D,
      surfaceDifferentialPullback_smul_D, surfaceDifferentialPullback_smul_D]
    have hn := regularSectionPullback_restrict_domain
      (Over.homMk f hbase : Over.mk surfaceToBase ⟶ Over.mk curveToBase) hWU V h
    exact congrArg₂ (fun c d => c • KaehlerDifferential.D ℂ Γ(surface, V) d)
      (AlgHom.congr_fun hn a) (AlgHom.congr_fun hn b)

/-- Restricting a pulled-back differential agrees with pulling back directly. -/
theorem surfaceDifferentialPullback_restrict (U : curve.Opens) {V W : surface.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (hWV : W ≤ V) (w : KaehlerDifferential ℂ Γ(curve, U)) :
    surfaceDifferentialRestriction hWV (surfaceDifferentialPullback f hbase U V h w) =
      surfaceDifferentialPullback f hbase U W (hWV.trans h) w := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ Γ(curve, U) w
  induction v using Finsupp.induction with
  | zero => simp
  | single_add b a v hb ha ih =>
    simp only [map_add, Finsupp.linearCombination_single, ih]
    congr 1
    rw [surfaceDifferentialPullback_smul_D, surfaceDifferentialRestriction_smul,
      surfaceDifferentialRestriction_D, surfaceDifferentialPullback_smul_D]
    have hn := regularSectionPullback_restrict
      (Over.homMk f hbase : Over.mk surfaceToBase ⟶ Over.mk curveToBase) U h hWV
    exact congrArg₂ (fun c d => c • KaehlerDifferential.D ℂ Γ(surface, W) d)
      (AlgHom.congr_fun hn a) (AlgHom.congr_fun hn b)

/-- The pullbacks of the two invariant forms agree wherever both chart formulas are defined. -/
theorem surfaceDifferentialPullback_overlap (V : surface.Opens)
    (hZ : V ≤ f ⁻¹ᵁ chart 2) (hY : V ≤ f ⁻¹ᵁ chart 1) :
    surfaceDifferentialPullback f hbase (chart 2) V hZ curveZDifferential =
      surfaceDifferentialPullback f hbase (chart 1) V hY curveYDifferential := by
  have hV : V ≤ f ⁻¹ᵁ (chart 2 ⊓ chart 1) := by
    rw [Scheme.Hom.preimage_inf]
    exact le_inf hZ hY
  have hw := congrArg (surfaceDifferentialPullback f hbase (chart 2 ⊓ chart 1) V hV)
    curveDifferential_overlap
  simpa only [surfaceDifferentialPullback_restrict_curve] using hw

end AlgebraicGeometry.ExplicitEllipticCandidate
