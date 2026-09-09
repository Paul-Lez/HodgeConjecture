/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceDifferential
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceInfinity
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Generation of the actual elliptic product-chart section ring

The affine pullback square gives a pushout of actual section rings. Consequently
the coordinate functions pulled from its two factors generate the product chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CommRingCat

/-- The two structure maps of a ring pushout generate the target as a ring. -/
theorem subring_eq_top_of_isPushout {A B C D : CommRingCat}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) (S : Subring D)
    (hi : ∀ b, i b ∈ S) (hj : ∀ c, j c ∈ S) : S = ⊤ := by
  let i' : B ⟶ CommRingCat.of S := CommRingCat.ofHom (i.hom.codRestrict S hi)
  let j' : C ⟶ CommRingCat.of S := CommRingCat.ofHom (j.hom.codRestrict S hj)
  have hc : f ≫ i' = g ≫ j' := by
    ext a
    exact congrArg (fun k => k a) h.w
  let l := h.desc i' j' hc
  have he : l ≫ CommRingCat.ofHom S.subtype = 𝟙 D := by
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc]
      rfl
    · rw [← Category.assoc, h.inr_desc]
      rfl
  apply top_unique
  intro d _
  have hd : ((l d : S) : D) = d := congrArg (fun k => k d) he
  exact hd ▸ (l d).property

end CommRingCat

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] regularSectionAlgebra

local instance surfaceCoordinateRingAlgebra (V : surface.Opens) : Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

local instance surfaceCoordinateBaseAffine : IsAffine base :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of ℂ)))

local instance surfaceCoordinateBaseTopAffine : IsAffine (⊤ : base.Opens).toScheme :=
  isAffineOpen_top base

/-- The actual section ring of the product Y chart is the pushout of the two curve rings. -/
theorem surfaceYChart_section_isPushout :
    IsPushout (curveToBase.appLE ⊤ (chart 1) (by simp))
      (curveToBase.appLE ⊤ (chart 1) (by simp))
      ((pullback.fst curveToBase curveToBase).appLE (chart 1)
        (surfaceDifferentialOpen (1, 1)) inf_le_left)
      ((pullback.snd curveToBase curveToBase).appLE (chart 1)
        (surfaceDifferentialOpen (1, 1)) inf_le_right) := by
  let H : IsPullback (pullback.fst curveToBase curveToBase)
      (pullback.snd curveToBase curveToBase) curveToBase curveToBase := .of_hasPullback _ _
  have h := isIso_pushoutSection_of_isAffineOpen H
    (US := ⊤) (UT := chart 1) (UX := chart 1)
    (UY := surfaceDifferentialOpen (1, 1)) (by simp) (by simp) rfl
    (isAffineOpen_top base) (chart_isAffineOpen 1) (chart_isAffineOpen 1)
  exact (isIso_pushoutSection_iff H (by simp) (by simp) rfl).mp h

/-- The Y product chart is an affine open of the actual surface. -/
theorem surfaceYChart_isAffineOpen : IsAffineOpen (surfaceDifferentialOpen (1, 1)) := by
  let H : IsPullback (pullback.fst curveToBase curveToBase)
      (pullback.snd curveToBase curveToBase) curveToBase curveToBase := .of_hasPullback _ _
  let : IsAffine (chart 1).toScheme := chart_isAffineOpen 1
  exact .of_isIso (Scheme.Hom.isPullback_resLE H
    (US := ⊤) (UT := chart 1) (UX := chart 1)
    (UY := surfaceDifferentialOpen (1, 1)) (by simp) (by simp) rfl).isoPullback.hom

/-- The polynomial map defined by all four actual projection-pulled coordinates. -/
def surfaceYPolynomialMap :
    MvPolynomial (Fin 2 × Fin 2) ℂ →ₐ[ℂ] Γ(surface, surfaceDifferentialOpen (1, 1)) :=
  MvPolynomial.aeval (fun ij => surfaceYCoordinate ij.1 ij.2)

@[simp] theorem surfaceYPolynomialMap_X (ij : Fin 2 × Fin 2) :
    surfaceYPolynomialMap (MvPolynomial.X ij) = surfaceYCoordinate ij.1 ij.2 := by
  simp [surfaceYPolynomialMap]

theorem surfaceYPolynomialMap_rename_left (p : MvPolynomial (Fin 2) ℂ) :
    surfaceYPolynomialMap (MvPolynomial.rename (fun j => ((0 : Fin 2), j)) p) =
      surfaceYCoordinateMapLeft p := by
  have h : surfaceYPolynomialMap.comp (MvPolynomial.rename (fun j => ((0 : Fin 2), j))) =
      surfaceYCoordinateMapLeft := by
    ext j
    simp
  exact AlgHom.congr_fun h p

theorem surfaceYPolynomialMap_rename_right (p : MvPolynomial (Fin 2) ℂ) :
    surfaceYPolynomialMap (MvPolynomial.rename (fun j => ((1 : Fin 2), j)) p) =
      surfaceYCoordinateMapRight p := by
  have h : surfaceYPolynomialMap.comp (MvPolynomial.rename (fun j => ((1 : Fin 2), j))) =
      surfaceYCoordinateMapRight := by
    ext j
    simp
  exact AlgHom.congr_fun h p

/-- The four coordinate functions generate the actual section ring of the Y product chart. -/
theorem surfaceYPolynomialMap_surjective : Function.Surjective surfaceYPolynomialMap := by
  have hr : surfaceYPolynomialMap.range.toSubring = ⊤ := by
    apply CommRingCat.subring_eq_top_of_isPushout surfaceYChart_section_isPushout
    · intro b
      obtain ⟨p, rfl⟩ := hypersurfaceCoordinateMap_surjective
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime) b
      exact ⟨MvPolynomial.rename (fun j => ((0 : Fin 2), j)) p,
        surfaceYPolynomialMap_rename_left p⟩
    · intro b
      obtain ⟨p, rfl⟩ := hypersurfaceCoordinateMap_surjective
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime) b
      exact ⟨MvPolynomial.rename (fun j => ((1 : Fin 2), j)) p,
        surfaceYPolynomialMap_rename_right p⟩
  intro s
  have hs : s ∈ surfaceYPolynomialMap.range.toSubring := by rw [hr]; trivial
  exact hs

end AlgebraicGeometry.ExplicitEllipticCandidate
