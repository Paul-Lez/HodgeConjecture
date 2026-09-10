/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticNestedTransitionClass
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Local vanishing of analytic degree-one extension classes

A degree-one sheaf cohomology class restricts to zero on some neighbourhood of every point.
The proof is purely sheaf-theoretic: represent the class in an injective resolution, use
exactness to factor its cocycle through the image of the preceding differential, and lift the
resulting image section locally along the epimorphism onto that image.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 10000

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (CommRingCat.of ℂ)))

local instance analyticExtLocallyZeroSheafAbelian : Abelian (AnalyticAdditiveSheaf X) :=
  CategoryTheory.sheafIsAbelian

local instance analyticExtLocallyZeroHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) :=
  analyticHasExt X

/-- Every degree-one extension class on an analytic open restricts to zero on some smaller
open neighbourhood of each specified point. -/
theorem analyticExtOne_locally_zero
    (F : AnalyticAdditiveSheaf X) (R : InjectiveResolution F)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (x : ComplexPoint X) (hx : x ∈ W)
    (α : Abelian.Ext.{1} (analyticOpenFreeAbelianSheaf X W) F 1) :
    ∃ (V : Opens (TopCat.of (ComplexPoint X))) (hVW : V ≤ W), x ∈ V ∧
      (Abelian.Ext.mk₀ (C := AnalyticAdditiveSheaf X)
        (analyticOpenFreeAbelianMap X (homOfLE hVW))).comp α
          (show 0 + 1 = 1 from rfl) = 0 := by
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α 2 rfl
  let S : ShortComplex (AnalyticAdditiveSheaf X) :=
    ShortComplex.mk (R.cocomplex.d 0 1) (R.cocomplex.d 1 2) (by simp)
  have hS : S.Exact := R.exact_succ 0
  let k : analyticOpenFreeAbelianSheaf X W ⟶ Abelian.image (R.cocomplex.d 0 1) :=
    hS.isLimitImage.lift (KernelFork.ofι f hf)
  have hk : k ≫ Abelian.image.ι (R.cocomplex.d 0 1) = f :=
    hS.isLimitImage.fac (KernelFork.ofι f hf) WalkingParallelPair.zero
  let t : (Abelian.image (R.cocomplex.d 0 1)).obj.obj (.op W) :=
    (analyticSectionSheafHomEquiv X (Abelian.image (R.cocomplex.d 0 1)) W).symm k
  have ht : analyticSectionSheafHom X (Abelian.image (R.cocomplex.d 0 1)) W t = k :=
    (analyticSectionSheafHomEquiv X (Abelian.image (R.cocomplex.d 0 1)) W).apply_symm_apply k
  have hepi : Epi (Abelian.factorThruImage (R.cocomplex.d 0 1)) := inferInstance
  have hlocal : TopCat.Presheaf.IsLocallySurjective
      (Abelian.factorThruImage (R.cocomplex.d 0 1)).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi
      (Abelian.factorThruImage (R.cocomplex.d 0 1))).mpr hepi
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hlocal
  obtain ⟨V, hVW, ⟨g, hg⟩, hxV⟩ := hlocal W t x hx
  refine ⟨V, hVW, hxV, ?_⟩
  rw [R.mk₀_comp_extMk]
  apply (R.extMk_eq_zero_iff
    (analyticOpenFreeAbelianMap X (homOfLE hVW) ≫ f) 2 rfl (by simp [hf]) 0 rfl).2
  refine ⟨analyticSectionSheafHom X (R.cocomplex.X 0) V g, ?_⟩
  rw [← hk]
  have hpre :
      analyticSectionSheafHom X (R.cocomplex.X 0) V g ≫
          Abelian.factorThruImage (R.cocomplex.d 0 1) =
        analyticOpenFreeAbelianMap X (homOfLE hVW) ≫ k := by
    rw [analyticSectionSheafHom_postcomp]
    rw [hg]
    rw [← ht, analyticOpenFreeAbelianMap_comp_section]
    rfl
  calc
    analyticSectionSheafHom X (R.cocomplex.X 0) V g ≫ R.cocomplex.d 0 1 =
        analyticSectionSheafHom X (R.cocomplex.X 0) V g ≫
          (Abelian.factorThruImage (R.cocomplex.d 0 1) ≫
            Abelian.image.ι (R.cocomplex.d 0 1)) := by rw [Abelian.image.fac]
    _ = (analyticSectionSheafHom X (R.cocomplex.X 0) V g ≫
          Abelian.factorThruImage (R.cocomplex.d 0 1)) ≫
            Abelian.image.ι (R.cocomplex.d 0 1) := (Category.assoc _ _ _).symm
    _ = (analyticOpenFreeAbelianMap X (homOfLE hVW) ≫ k) ≫
          Abelian.image.ι (R.cocomplex.d 0 1) := by rw [hpre]
    _ = analyticOpenFreeAbelianMap X (homOfLE hVW) ≫
          (k ≫ Abelian.image.ι (R.cocomplex.d 0 1)) := Category.assoc _ _ _

end AlgebraicGeometry.ComplexPoint
