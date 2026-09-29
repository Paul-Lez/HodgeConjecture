/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Basic
public import Other.Oka.Analytification.SchemeAffine

/-!
# Projective space over `ℂ` as a scheme locally of finite type

`ComplexAnalytic.projectiveSpace n` is `ℙₒ(n; ℂ) = Proj ℂ[X₀, …, Xₙ]` (with `ℂ` lifted to
universe `u`), as an object of `ComplexAnalytic.SchemeLFTℂ.{u}`; its structure morphism is proper
(`ComplexAnalytic.isProper_projectiveSpace_hom`). The standard charts are morphisms
`ComplexAnalytic.projectiveSpaceChart i : affineSpace n ⟶ projectiveSpace n` over `ℂ` from affine
space `affineSpace n = Spec ℂ[Y₀, …, Yₙ₋₁]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- **Affine `n`-space over `ℂ`**, `Spec ℂ[Y₀, …, Yₙ₋₁]`, as a scheme locally of finite type. -/
noncomputable def affineSpace (n : ℕ) : SchemeLFTℂ.{u} :=
  SchemeLFTℂ.spec (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := ULift.{u} ℂ)))
    (RingHom.finiteType_algebraMap.mpr inferInstance)

@[simp]
lemma affineSpace_obj_hom (n : ℕ) :
    (affineSpace.{u} n).obj.hom = Spec.map (CommRingCat.ofHom MvPolynomial.C) :=
  rfl

/-- **Projective `n`-space over `ℂ`**, `Proj ℂ[X₀, …, Xₙ]`, as a scheme locally of finite type. -/
noncomputable def projectiveSpace (n : ℕ) : SchemeLFTℂ.{u} :=
  ⟨Over.mk (ProjectiveSpace.toSpec n (ULift.{u} ℂ)),
    show LocallyOfFiniteType (ProjectiveSpace.toSpec n _) from inferInstance⟩

@[simp]
lemma projectiveSpace_obj_left (n : ℕ) :
    (projectiveSpace.{u} n).obj.left = ℙₒ(n; ULift.{u} ℂ) :=
  rfl

@[simp]
lemma projectiveSpace_obj_hom (n : ℕ) :
    (projectiveSpace.{u} n).obj.hom = ProjectiveSpace.toSpec n (ULift.{u} ℂ) :=
  rfl

instance isProper_projectiveSpace_hom (n : ℕ) : IsProper (projectiveSpace.{u} n).obj.hom :=
  inferInstanceAs (IsProper (ProjectiveSpace.toSpec n _))

/-- The **standard chart** `i` of `ℙⁿ`, `𝔸ⁿ ⟶ ℙⁿ` over `ℂ`, an open immersion onto
`ProjectiveSpace.U n _ i = D₊(Xᵢ)`. -/
noncomputable def projectiveSpaceChart {n : ℕ} (i : Fin (n + 1)) :
    affineSpace.{u} n ⟶ projectiveSpace.{u} n :=
  ObjectProperty.homMk (Over.homMk (ProjectiveSpace.chart i) (ProjectiveSpace.chart_toSpec i))

@[simp]
lemma projectiveSpaceChart_hom_left {n : ℕ} (i : Fin (n + 1)) :
    (projectiveSpaceChart.{u} i).hom.left = ProjectiveSpace.chart i :=
  rfl

instance {n : ℕ} (i : Fin (n + 1)) : IsOpenImmersion (projectiveSpaceChart.{u} i).hom.left :=
  inferInstanceAs (IsOpenImmersion (ProjectiveSpace.chart i))

end ComplexAnalytic

end
