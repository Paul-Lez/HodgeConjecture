/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLineBundleSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Holomorphic line-bundle sections as a sheaf of modules

Pointwise multiplication by a holomorphic function preserves holomorphic sections.
The section sheaf therefore carries its natural module structure over the holomorphic
structure sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Bundle
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance holomorphicLineBundleModuleTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- The holomorphic structure sheaf, regarded as a sheaf of rings. -/
def holomorphicRingSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) RingCat :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (forget₂ CommRingCat RingCat)).obj (holomorphicFunctionSheaf X d)

namespace HolomorphicUnitExtension

variable {X d} (E : HolomorphicUnitExtension X d)

local instance sectionCoordinatesModule (U : Opens (TopCat.of (ComplexPoint X))) :
    Module (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) (U → ℂ) :=
  Module.compHom (U → ℂ) ContMDiffMap.coeFnRingHom

/-- A holomorphic scalar extended by zero remains holomorphic at every point of its domain. -/
theorem contMDiffAt_extendSection_scalar (U : Opens (TopCat.of (ComplexPoint X)))
    (a : C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) (x : U) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω
      (fun y => (E.extendSection U a y : ℂ)) x := by
  apply (contMDiffAt_subtype_iff (U := U) (x := x)).mp
  have hfun : (fun z : U => (E.extendSection U a z : ℂ)) = a := by
    funext z
    exact E.extendSection_of_mem U a z z.property
  rw [hfun]
  exact a.contMDiff.contMDiffAt

/-- Holomorphic sections are stable under multiplication by holomorphic functions. -/
def sectionSubmodule (U : Opens (TopCat.of (ComplexPoint X))) :
    Submodule (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) (U → ℂ) where
  __ := E.sectionAddSubgroup U
  smul_mem' a f hf := by
    intro x
    have h : E.extendSection U (a • f) = fun y =>
        @SMul.smul ℂ (E.lineBundleCore.Fiber y) _
          (E.extendSection U a y) (E.extendSection U f y) := by
      funext y
      by_cases hy : y ∈ U
      · rw [E.extendSection_of_mem U (a • f) y hy, E.extendSection_of_mem U a y hy,
          E.extendSection_of_mem U f y hy]
        rfl
      · rw [E.extendSection_of_notMem U (a • f) y hy, E.extendSection_of_notMem U a y hy,
          E.extendSection_of_notMem U f y hy]
        change (0 : ℂ) = 0 * 0
        simp
    change ContMDiffAt _ _ _ (fun y => TotalSpace.mk' ℂ y (E.extendSection U (a • f) y)) _
    rw [h]
    exact (E.contMDiffAt_extendSection_scalar U a x).smul_section (hf x)

/-- Sections over `U` form a module over the holomorphic functions on `U`. -/
instance holomorphicSections_module (U : Opens (TopCat.of (ComplexPoint X))) :
    Module (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) (E.HolomorphicSections U) :=
  inferInstanceAs (Module (C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯) ↥(E.sectionSubmodule U))

/-- The same module structure with the scalar ring expressed through the structure sheaf. -/
instance holomorphicSections_ringModule (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Module ((holomorphicRingSheaf X d).obj.obj U) (E.HolomorphicSections (unop U)) :=
    inferInstanceAs (Module (C^ω⟮𝓘(ℂ, Fin d → ℂ),
      (unop U : Opens (TopCat.of (ComplexPoint X))); ℂ⟯) (E.HolomorphicSections (unop U)))

/-- The module of holomorphic sections with the structure sheaf's ring as scalar ring. -/
def sectionModule (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    ModuleCat ((holomorphicRingSheaf X d).obj.obj U) :=
  ModuleCat.of _ (E.HolomorphicSections (unop U))

/-- Restriction of sections is linear after restricting scalars. -/
def sectionModuleRestriction {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) :
    E.sectionModule U ⟶ (ModuleCat.restrictScalars ((holomorphicRingSheaf X d).obj.map i).hom).obj
      (E.sectionModule V) := by
  letI : Module ((holomorphicRingSheaf X d).obj.obj U) (E.sectionModule V) :=
    Module.compHom (E.sectionModule V) ((holomorphicRingSheaf X d).obj.map i).hom
  refine ModuleCat.ofHom ?_
  exact
    { toFun := E.sectionRestriction i.unop
      map_add' := (E.sectionRestriction i.unop).map_add
      map_smul' := fun _ _ => rfl }

/-- The presheaf of modules formed by holomorphic sections. -/
def sectionPresheafOfModules : PresheafOfModules (holomorphicRingSheaf X d).obj where
  obj := E.sectionModule
  map := E.sectionModuleRestriction
  map_id _ := rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl

/-- The holomorphic line bundle's sheaf of modules over the holomorphic structure sheaf. -/
def sectionSheafOfModules : SheafOfModules (holomorphicRingSheaf X d) where
  val := E.sectionPresheafOfModules
  isSheaf := E.sectionSheaf.property

end HolomorphicUnitExtension

end AlgebraicGeometry.ComplexPoint
