/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare
public import HodgeConjecture.Mathlib.Algebra.Category.Grp.Basic
public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# The holomorphic de Rham complex

This file assembles the analytic differential forms constructed from actual manifold derivatives
into a presheaf complex and then sheafifies it degree by degree. Restriction of functions induces
restriction of forms and commutes with the exterior derivative.

Constant complex-valued functions define a canonical morphism from the constant sheaf complex to
the holomorphic de Rham complex. Both complexes are also extended by zero to integer degrees for
use in the derived category. No differential forms, differentials, or comparison maps are supplied
as data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)

local instance holomorphicDeRhamTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

local instance holomorphicDeRhamChartedSpace [SmoothOfRelativeDimension d structureMap] :
    ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
  analyticChartedSpace structureMap d

/-- Holomorphic de Rham forms in a fixed degree, as a presheaf of complex vector spaces.

This is the coefficient-aware object.  It is the migration target for the additive presheaf used
by the existing derived comparison below, and keeps the linearity of restriction maps available
for module-valued sheafification. -/
def holomorphicDeRhamModulePresheaf [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X structureMap)) where
  obj U := ModuleCat.of ℂ
    (HolomorphicForm structureMap d U p)
  map {U V} i := ModuleCat.ofHom
    (holomorphicFormRestriction structureMap d i p)
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [holomorphicFormRestriction_id]
    rfl
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [holomorphicFormRestriction_comp]
    rfl

/-- The legacy additive-group presentation of the holomorphic de Rham presheaf. -/
def holomorphicDeRhamPresheaf [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)) where
  obj U := AddCommGrpCat.of
    (HolomorphicForm structureMap d U p)
  map {U V} i := AddCommGrpCat.ofHom
    (holomorphicFormRestriction structureMap d i p).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.hom_ext
    change (holomorphicFormRestriction structureMap d (𝟙 U) p).toAddMonoidHom = _
    rw [holomorphicFormRestriction_id]
    rfl
  map_comp i j := by
    apply AddCommGrpCat.hom_ext
    change (holomorphicFormRestriction structureMap d (i ≫ j) p).toAddMonoidHom = _
    rw [holomorphicFormRestriction_comp]
    rfl

/-- Holomorphic differential forms vanish in degrees above the complex dimension, already before
sheafification. -/
lemma holomorphicDeRhamPresheaf_isZero_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    IsZero (holomorphicDeRhamPresheaf structureMap d p) := by
  apply Functor.isZero
  intro U
  let : Subsingleton ((holomorphicDeRhamPresheaf structureMap d p).obj U) :=
    ⟨fun x y => by
      rw [holomorphicForm_eq_zero_of_lt structureMap d U hp x,
        holomorphicForm_eq_zero_of_lt structureMap d U hp y]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The exterior derivative as a morphism of presheaves. -/
def holomorphicDeRhamModuleDifferential [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    holomorphicDeRhamModulePresheaf structureMap d p ⟶
      holomorphicDeRhamModulePresheaf structureMap d (p + 1) where
  app U := ModuleCat.ofHom <|
    holomorphicFormDifferential structureMap d U p
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (holomorphicFormRestriction_differential structureMap d i p x).symm

lemma holomorphicDeRhamModuleDifferential_comp
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    holomorphicDeRhamModuleDifferential structureMap d p ≫
      holomorphicDeRhamModuleDifferential structureMap d (p + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact holomorphicFormDifferential_squared structureMap d U p x

/-- The legacy additive presentation of the exterior derivative. -/
def holomorphicDeRhamDifferential [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    holomorphicDeRhamPresheaf structureMap d p ⟶
      holomorphicDeRhamPresheaf structureMap d (p + 1) where
  app U := AddCommGrpCat.ofHom <|
    (holomorphicFormDifferential structureMap d U p).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact (holomorphicFormRestriction_differential structureMap d i p x).symm

lemma holomorphicDeRhamDifferential_comp [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    holomorphicDeRhamDifferential structureMap d p ≫
      holomorphicDeRhamDifferential structureMap d (p + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact holomorphicFormDifferential_squared structureMap d U p x

/-- The holomorphic de Rham complex before forgetting its complex-linear structure. -/
def holomorphicDeRhamModulePresheafComplex [SmoothOfRelativeDimension d structureMap] :
    CochainComplex
      (TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X structureMap))) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamModulePresheaf structureMap d)
    (holomorphicDeRhamModuleDifferential structureMap d)
    (by
      intro p
      apply NatTrans.ext
      funext U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact holomorphicFormDifferential_squared structureMap d U p x)

/-- The holomorphic de Rham complex before sheafification. -/
def holomorphicDeRhamPresheafComplex [SmoothOfRelativeDimension d structureMap] :
    CochainComplex
      (TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamPresheaf structureMap d)
    (holomorphicDeRhamDifferential structureMap d)
    (holomorphicDeRhamDifferential_comp structureMap d)

@[simp] lemma holomorphicDeRhamPresheafComplex_d
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    (holomorphicDeRhamPresheafComplex structureMap d).d p (p + 1) =
      holomorphicDeRhamDifferential structureMap d p := by
  simp [holomorphicDeRhamPresheafComplex]

/-- The constant presheaf of additive groups with value `ℂ`. -/
def constantComplexAddCommGrpPresheaf :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)) :=
  (Functor.const (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ).obj
    (AddCommGrpCat.of ℂ)

/-- The constant presheaf with value `ℂ`, retaining its complex-module structure. -/
def constantComplexModulePresheaf :
    TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X structureMap)) :=
  (Functor.const (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ).obj
    (ModuleCat.of ℂ ℂ)

/-- Complex-linear constants as holomorphic de Rham forms of degree zero. -/
def constantsToHolomorphicDeRhamModuleZero [SmoothOfRelativeDimension d structureMap] :
    constantComplexModulePresheaf structureMap ⟶
      holomorphicDeRhamModulePresheaf structureMap d 0 where
  app U := ModuleCat.ofHom
    (holomorphicFormOfConstant structureMap d U)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (holomorphicFormRestriction_ofConstant structureMap d i c).symm

lemma constantsToHolomorphicDeRhamModuleZero_comp_differential
    [SmoothOfRelativeDimension d structureMap] :
    constantsToHolomorphicDeRhamModuleZero structureMap d ≫
      holomorphicDeRhamModuleDifferential structureMap d 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact holomorphicFormDifferential_ofConstant structureMap d U c

/-- The complex-linear inclusion of constants in the module-valued de Rham complex. -/
def constantsToHolomorphicDeRhamModulePresheafComplex
    [SmoothOfRelativeDimension d structureMap] :
    (CochainComplex.single₀
      (TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X structureMap)))).obj
        (constantComplexModulePresheaf structureMap) ⟶
      holomorphicDeRhamModulePresheafComplex structureMap d :=
  HomologicalComplex.mkHomFromSingle
    (constantsToHolomorphicDeRhamModuleZero structureMap d) <| by
      intro k hk
      obtain rfl : k = 1 := by simpa using hk.symm
      change constantsToHolomorphicDeRhamModuleZero structureMap d ≫
        holomorphicDeRhamModuleDifferential structureMap d 0 = 0
      exact constantsToHolomorphicDeRhamModuleZero_comp_differential structureMap d

/-- Constants as holomorphic de Rham forms of degree zero. -/
def constantsToHolomorphicDeRhamZero [SmoothOfRelativeDimension d structureMap] :
    constantComplexAddCommGrpPresheaf structureMap ⟶
      holomorphicDeRhamPresheaf structureMap d 0 where
  app U := AddCommGrpCat.ofHom
    (holomorphicFormOfConstant structureMap d U).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro c
    exact (holomorphicFormRestriction_ofConstant structureMap d i c).symm

/-- On a nonempty open set, distinct complex constants define distinct holomorphic zero-forms. -/
lemma holomorphicFormOfConstant_injective [SmoothOfRelativeDimension d structureMap]
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ) [Nonempty U.unop] :
    Function.Injective (holomorphicFormOfConstant structureMap d U) := by
  intro c c' hcc'
  have hzero : holomorphicFormOfConstant structureMap d U (c - c') = 0 := by
    rw [map_sub, hcc', sub_self]
  let a : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions structureMap d U) 0 :=
    Finsupp.single
      (algebraMap ℂ (OpenHolomorphicFunctions structureMap d U) (c - c'), Fin.elim0) 1
  have ha : a ∈ holomorphicFormRelations structureMap d U 0 := by
    change Submodule.Quotient.mk a = 0 at hzero
    rw [Submodule.Quotient.mk_eq_zero] at hzero
    exact hzero
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel,
    restrictionStableAnalyticKernel] at ha
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at ha
  specialize ha U (𝟙 U)
  rw [rawRestriction_id, LinearMap.id_apply] at ha
  let x : U.unop := Classical.arbitrary U.unop
  let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
  have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
  have hxe : e x.1 ∈ chartSectionDomain structureMap d U x.1 := by
    refine ⟨mem_extChartAt_target x.1, ?_⟩
    change e.symm (e x.1) ∈ U.unop
    rw [e.left_inv hxsource]
    exact x.2
  have heval := (mem_chartEvaluationKernel_iff structureMap d U 0 a).1 ha
    x.1 (e x.1) hxe
  rw [chartRawEvaluation_rawConstant structureMap d U x.1 (c - c') hxe] at heval
  have hcoeff := congrArg
    (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
  have : c - c' = 0 := by simpa using hcoeff
  exact sub_eq_zero.mp this

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of complex constants into holomorphic zero-forms is a monomorphism on every
stalk. -/
lemma constantsToHolomorphicDeRhamZero_stalk_mono
    [SmoothOfRelativeDimension d structureMap] (x : ComplexPoint X structureMap) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (constantsToHolomorphicDeRhamZero structureMap d)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro z z' h
  obtain ⟨U, hxU, c, rfl⟩ := (constantComplexAddCommGrpPresheaf structureMap).exists_germ_eq z
  obtain ⟨V, hxV, c', rfl⟩ := (constantComplexAddCommGrpPresheaf structureMap).exists_germ_eq z'
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
    (holomorphicDeRhamPresheaf structureMap d 0).germ_eq x hxU hxV
      ((constantsToHolomorphicDeRhamZero structureMap d).app (.op U) c)
      ((constantsToHolomorphicDeRhamZero structureMap d).app (.op V) c') h
  let _ : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hcc' : c = c' := by
    apply holomorphicFormOfConstant_injective structureMap d (.op W)
    have hc := congrArg (fun k :
        (constantComplexAddCommGrpPresheaf structureMap).obj (.op U) ⟶
          (holomorphicDeRhamPresheaf structureMap d 0).obj (.op W) ↦ k c)
      ((constantsToHolomorphicDeRhamZero structureMap d).naturality iWU.op)
    have hc' := congrArg (fun k :
        (constantComplexAddCommGrpPresheaf structureMap).obj (.op V) ⟶
          (holomorphicDeRhamPresheaf structureMap d 0).obj (.op W) ↦ k c')
      ((constantsToHolomorphicDeRhamZero structureMap d).naturality iWV.op)
    change holomorphicFormOfConstant structureMap d (.op W) c =
      (holomorphicDeRhamPresheaf structureMap d 0).map iWU.op
        ((constantsToHolomorphicDeRhamZero structureMap d).app (.op U) c) at hc
    change holomorphicFormOfConstant structureMap d (.op W) c' =
      (holomorphicDeRhamPresheaf structureMap d 0).map iWV.op
        ((constantsToHolomorphicDeRhamZero structureMap d).app (.op V) c') at hc'
    exact hc.trans (hW.trans hc'.symm)
  subst c'
  rw [← (constantComplexAddCommGrpPresheaf structureMap).germ_res_apply iWU x hxW,
    ← (constantComplexAddCommGrpPresheaf structureMap).germ_res_apply iWV x hxW]
  rfl

lemma constantsToHolomorphicDeRhamZero_comp_differential
    [SmoothOfRelativeDimension d structureMap] :
    constantsToHolomorphicDeRhamZero structureMap d ≫
      holomorphicDeRhamDifferential structureMap d 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  exact holomorphicFormDifferential_ofConstant structureMap d U c

/-- The inclusion of the constant presheaf into the holomorphic de Rham complex. -/
def constantsToHolomorphicDeRhamPresheafComplex
    [SmoothOfRelativeDimension d structureMap] :
    (CochainComplex.single₀
      (TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)))).obj
        (constantComplexAddCommGrpPresheaf structureMap) ⟶
      holomorphicDeRhamPresheafComplex structureMap d :=
  HomologicalComplex.mkHomFromSingle
    (constantsToHolomorphicDeRhamZero structureMap d) <| by
      intro k hk
      obtain rfl : k = 1 := by simpa using hk.symm
      change constantsToHolomorphicDeRhamZero structureMap d ≫
        (holomorphicDeRhamPresheafComplex structureMap d).d 0 1 = 0
      rw [holomorphicDeRhamPresheafComplex_d]
      exact constantsToHolomorphicDeRhamZero_comp_differential structureMap d

/-- Holomorphic de Rham forms in a fixed degree, after additive sheafification. -/
def holomorphicDeRhamSheaf [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (presheafToSheaf J AddCommGrpCat).obj
    (holomorphicDeRhamPresheaf structureMap d p)

/-- The sheaf of holomorphic `p`-forms is zero for `p` above the complex dimension. -/
lemma holomorphicDeRhamSheaf_isZero_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    IsZero (holomorphicDeRhamSheaf structureMap d p) := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  exact (presheafToSheaf J AddCommGrpCat).map_isZero
    (holomorphicDeRhamPresheaf_isZero_of_lt structureMap d hp)

/-- The sheafified exterior derivative. -/
def holomorphicDeRhamSheafDifferential [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    holomorphicDeRhamSheaf structureMap d p ⟶
      holomorphicDeRhamSheaf structureMap d (p + 1) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (presheafToSheaf J AddCommGrpCat).map
    (holomorphicDeRhamDifferential structureMap d p)

/-- The sheafified holomorphic de Rham complex. -/
def holomorphicDeRhamComplex [SmoothOfRelativeDimension d structureMap] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamSheaf structureMap d)
    (holomorphicDeRhamSheafDifferential structureMap d)
    (fun p => by
      let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
      change (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential structureMap d p) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential structureMap d (p + 1)) = 0
      rw [← Functor.map_comp, holomorphicDeRhamDifferential_comp, Functor.map_zero])

@[simp] lemma holomorphicDeRhamComplex_d [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    (holomorphicDeRhamComplex structureMap d).d p (p + 1) =
      holomorphicDeRhamSheafDifferential structureMap d p := by
  simp [holomorphicDeRhamComplex]

/-- A neighborhood-wise primitive for every local kernel section gives exactness on a stalk.
The primitive may be taken after shrinking the original neighborhood. -/
lemma holomorphicStalkExact_of_locallyPrimitive
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat
      (TopCat.of (ComplexPoint X structureMap))))
    (hlocal : ∀ (x : ComplexPoint X structureMap)
      (U : Opens (TopCat.of (ComplexPoint X structureMap))) (_hx : x ∈ U)
      (s : S.X₂.obj (.op U)), S.g.app (.op U) s = 0 →
        ∃ (V : Opens (TopCat.of (ComplexPoint X structureMap))) (_hxV : x ∈ V)
          (i : V ⟶ U) (t : S.X₁.obj (.op V)),
          S.f.app (.op V) t = S.X₂.map i.op s)
    (x : ComplexPoint X structureMap) :
    (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq z
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g
      (S.X₂.germ U x hxU s) = 0 at hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
  have hz' : S.X₃.germ U x hxU (S.g.app (.op U) s) =
      S.X₃.germ U x hxU 0 := by
    rw [map_zero]
    exact hz
  obtain ⟨W, hxW, iWU, iWU', hW⟩ :=
    S.X₃.germ_eq x hxU hxU (S.g.app (.op U) s) 0 hz'
  have hWs : S.g.app (.op W) (S.X₂.map iWU.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.naturality, ConcreteCategory.comp_apply]
    simpa using hW
  obtain ⟨V, hxV, iVW, t, ht⟩ :=
    hlocal x W hxW (S.X₂.map iWU.op s) hWs
  refine ⟨S.X₁.germ V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f
      (S.X₁.germ V x hxV t) = S.X₂.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    S.X₂.germ_res_apply iVW x hxV, S.X₂.germ_res_apply iWU x hxW]

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise sheafification unit from holomorphic forms to the underlying presheaf of the
holomorphic de Rham sheaf complex. -/
noncomputable def holomorphicDeRhamSheafificationUnit
    [SmoothOfRelativeDimension d structureMap] :
    holomorphicDeRhamPresheafComplex structureMap d ⟶
      (TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X structureMap))).mapHomologicalComplex
          (ComplexShape.up ℕ) |>.obj (holomorphicDeRhamComplex structureMap d) where
  f p := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    (holomorphicDeRhamPresheaf structureMap d p)
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, holomorphicDeRhamPresheafComplex_d,
      holomorphicDeRhamComplex_d]
    dsimp [holomorphicDeRhamSheafDifferential, holomorphicDeRhamSheaf]
    exact (toSheafify_naturality
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      (holomorphicDeRhamDifferential structureMap d i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified holomorphic de Rham complex is exact in every positive degree. -/
lemma holomorphicDeRhamComplex_exactAt_succ
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    (holomorphicDeRhamComplex structureMap d).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := holomorphicDeRhamComplex structureMap d)
    (i := p) (j := p + 1) (k := (p + 1) + 1) (by simp) (by simp)]
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let P := holomorphicDeRhamPresheafComplex structureMap d
  have hP : (P.sc' p (p + 1) ((p + 1) + 1)).map stalk |>.Exact :=
    holomorphicStalkExact_of_locallyPrimitive structureMap
      (P.sc' p (p + 1) ((p + 1) + 1)) (by
        intro y U hyU form hform
        dsimp [P, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'] at hform ⊢
        rw [holomorphicDeRhamPresheafComplex_d] at hform
        rw [holomorphicDeRhamPresheafComplex_d]
        change holomorphicFormDifferential structureMap d (.op U) (p + 1) form = 0 at hform
        obtain ⟨W, k, θ, hyW, hθ⟩ :=
          exists_local_holomorphicForm_primitive structureMap d (.op U) y hyU p form hform
        exact ⟨W.unop, hyW, k.unop, θ, hθ⟩) x
  let unit := holomorphicDeRhamSheafificationUnit structureMap d
  let stalkUnit := (stalk.mapHomologicalComplex (ComplexShape.up ℕ)).map unit
  let η := (HomologicalComplex.shortComplexFunctor' AddCommGrpCat
    (ComplexShape.up ℕ) p (p + 1) ((p + 1) + 1)).map stalkUnit
  let _ : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf structureMap d p)
  let _ : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf structureMap d (p + 1))
  let _ : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf structureMap d ((p + 1) + 1))
  let _ : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

/-- The holomorphic de Rham complex is exact in every degree above the complex dimension. -/
lemma holomorphicDeRhamComplex_exactAt_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    (holomorphicDeRhamComplex structureMap d).ExactAt p :=
  HomologicalComplex.ExactAt.of_isZero
    (holomorphicDeRhamSheaf_isZero_of_lt structureMap d hp)

/-- Multiplication by a complex scalar on the presheaf of holomorphic de Rham forms. -/
def scalarHolomorphicDeRhamPresheaf [SmoothOfRelativeDimension d structureMap]
    (p : ℕ) (c : ℂ) :
    holomorphicDeRhamPresheaf structureMap d p ⟶
      holomorphicDeRhamPresheaf structureMap d p where
  app U := AddCommGrpCat.ofHom
    ((c • LinearMap.id : HolomorphicForm structureMap d U p →ₗ[ℂ] _).toAddMonoidHom)
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    dsimp [holomorphicDeRhamPresheaf] at x ⊢
    change c • holomorphicFormRestriction structureMap d i p x =
      holomorphicFormRestriction structureMap d i p (c • x)
    exact (LinearMap.map_smul _ c x).symm

@[simp] lemma scalarHolomorphicDeRhamPresheaf_apply
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) (c : ℂ)
    (U : (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ)
    (x : HolomorphicForm structureMap d U p) :
    (scalarHolomorphicDeRhamPresheaf structureMap d p c).app U x = c • x := by
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_zero
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    scalarHolomorphicDeRhamPresheaf structureMap d p 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_one
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    scalarHolomorphicDeRhamPresheaf structureMap d p 1 = 𝟙 _ := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_add
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) (a b : ℂ) :
    scalarHolomorphicDeRhamPresheaf structureMap d p (a + b) =
      scalarHolomorphicDeRhamPresheaf structureMap d p a +
        scalarHolomorphicDeRhamPresheaf structureMap d p b := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp [add_smul]
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_mul
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) (a b : ℂ) :
    scalarHolomorphicDeRhamPresheaf structureMap d p (a * b) =
      scalarHolomorphicDeRhamPresheaf structureMap d p b ≫
        scalarHolomorphicDeRhamPresheaf structureMap d p a := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp [mul_smul]
  rfl

/-- Scalar multiplication commutes with the exterior derivative. -/
lemma scalarHolomorphicDeRhamPresheaf_d
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) (c : ℂ) :
    scalarHolomorphicDeRhamPresheaf structureMap d p c ≫
      holomorphicDeRhamDifferential structureMap d p =
    holomorphicDeRhamDifferential structureMap d p ≫
      scalarHolomorphicDeRhamPresheaf structureMap d (p + 1) c := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact (holomorphicFormDifferential structureMap d U p).map_smul c x

/-- Multiplication by a complex scalar as an endomorphism of the presheaf de Rham complex. -/
def scalarHolomorphicDeRhamPresheafComplex
    [SmoothOfRelativeDimension d structureMap] (c : ℂ) :
    holomorphicDeRhamPresheafComplex structureMap d ⟶
      holomorphicDeRhamPresheafComplex structureMap d := by
  unfold holomorphicDeRhamPresheafComplex
  exact CochainComplex.ofHom
    (fun p => scalarHolomorphicDeRhamPresheaf structureMap d p c)
    (fun p => by
      simpa [CochainComplex.of_d] using
        scalarHolomorphicDeRhamPresheaf_d structureMap d p c)

/-- Multiplication by a complex scalar as an endomorphism of the sheafified de Rham complex. -/
def scalarHolomorphicDeRhamComplex [SmoothOfRelativeDimension d structureMap]
    (c : ℂ) :
    holomorphicDeRhamComplex structureMap d ⟶
      holomorphicDeRhamComplex structureMap d := by
  unfold holomorphicDeRhamComplex
  exact CochainComplex.ofHom
    (fun p =>
      let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X structureMap))
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf structureMap d p c))
    (fun p => by
      let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X structureMap))
      simp only [CochainComplex.of_d]
      change (presheafToSheaf J AddCommGrpCat).map
          (scalarHolomorphicDeRhamPresheaf structureMap d p c) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential structureMap d p) =
        (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential structureMap d p) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (scalarHolomorphicDeRhamPresheaf structureMap d (p + 1) c)
      rw [← Functor.map_comp, ← Functor.map_comp,
        scalarHolomorphicDeRhamPresheaf_d])

@[simp] lemma scalarHolomorphicDeRhamComplex_zero
    [SmoothOfRelativeDimension d structureMap] :
    scalarHolomorphicDeRhamComplex structureMap d 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf structureMap d p 0) = 0
  rw [scalarHolomorphicDeRhamPresheaf_zero, Functor.map_zero]

@[simp] lemma scalarHolomorphicDeRhamComplex_one
    [SmoothOfRelativeDimension d structureMap] :
    scalarHolomorphicDeRhamComplex structureMap d 1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf structureMap d p 1) = 𝟙 _
  rw [scalarHolomorphicDeRhamPresheaf_one]
  exact (presheafToSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    AddCommGrpCat).map_id _

@[simp] lemma scalarHolomorphicDeRhamComplex_add
    [SmoothOfRelativeDimension d structureMap] (a b : ℂ) :
    scalarHolomorphicDeRhamComplex structureMap d (a + b) =
      scalarHolomorphicDeRhamComplex structureMap d a +
        scalarHolomorphicDeRhamComplex structureMap d b := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf structureMap d p (a + b)) = _
  rw [scalarHolomorphicDeRhamPresheaf_add, Functor.map_add]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplex_mul
    [SmoothOfRelativeDimension d structureMap] (a b : ℂ) :
    scalarHolomorphicDeRhamComplex structureMap d (a * b) =
      scalarHolomorphicDeRhamComplex structureMap d b ≫
        scalarHolomorphicDeRhamComplex structureMap d a := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf structureMap d p (a * b)) = _
  rw [scalarHolomorphicDeRhamPresheaf_mul, Functor.map_comp]
  rfl

/-- The constant sheaf with value the additive group of complex numbers. -/
def constantComplexSheaf :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℂ)

/-- Multiplication by a complex scalar as an additive endomorphism of `ℂ`. -/
def complexScalarAddHom (c : ℂ) : ℂ →+ ℂ :=
  DistribSMul.toAddMonoidHom ℂ c

/-- Scalar multiplication on the constant complex presheaf. -/
def complexScalarPresheaf (c : ℂ) :
    constantComplexAddCommGrpPresheaf structureMap ⟶
      constantComplexAddCommGrpPresheaf structureMap where
  app _ := AddCommGrpCat.ofHom (complexScalarAddHom c)
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    rfl

/-- Scalar multiplication on the constant complex sheaf. -/
def complexScalarSheaf (c : ℂ) :
    constantComplexSheaf structureMap ⟶ constantComplexSheaf structureMap := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X structureMap))
  exact (presheafToSheaf J AddCommGrpCat).map
    (complexScalarPresheaf structureMap c)

/-- The sheafified inclusion of constants as de Rham zero-forms. -/
def constantsToHolomorphicDeRhamZeroSheaf [SmoothOfRelativeDimension d structureMap] :
    constantComplexSheaf structureMap ⟶ holomorphicDeRhamSheaf structureMap d 0 :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  (presheafToSheaf J AddCommGrpCat).map
    (constantsToHolomorphicDeRhamZero structureMap d)

lemma constantsToHolomorphicDeRhamZeroSheaf_comp_differential
    [SmoothOfRelativeDimension d structureMap] :
    constantsToHolomorphicDeRhamZeroSheaf structureMap d ≫
      holomorphicDeRhamSheafDifferential structureMap d 0 = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap))
  change (presheafToSheaf J AddCommGrpCat).map
      (constantsToHolomorphicDeRhamZero structureMap d) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (holomorphicDeRhamDifferential structureMap d 0) = 0
  rw [← Functor.map_comp, constantsToHolomorphicDeRhamZero_comp_differential,
    Functor.map_zero]

/-- The augmented holomorphic de Rham short complex before sheafification. -/
noncomputable def constantsToHolomorphicDeRhamPresheafShortComplex
    [SmoothOfRelativeDimension d structureMap] :
    ShortComplex (TopCat.Presheaf AddCommGrpCat
      (TopCat.of (ComplexPoint X structureMap))) :=
  ShortComplex.mk (constantsToHolomorphicDeRhamZero structureMap d)
    (holomorphicDeRhamDifferential structureMap d 0)
    (constantsToHolomorphicDeRhamZero_comp_differential structureMap d)

/-- The augmented holomorphic de Rham short complex after sheafification. -/
noncomputable def constantsToHolomorphicDeRhamSheafShortComplex
    [SmoothOfRelativeDimension d structureMap] :
    ShortComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (ComplexPoint X structureMap))) :=
  ShortComplex.mk (constantsToHolomorphicDeRhamZeroSheaf structureMap d)
    (holomorphicDeRhamSheafDifferential structureMap d 0)
    (constantsToHolomorphicDeRhamZeroSheaf_comp_differential structureMap d)

set_option backward.isDefEq.respectTransparency false in
/-- The sheafification unit between the augmented presheaf and sheaf short complexes. -/
noncomputable def constantsToHolomorphicDeRhamShortComplexSheafificationUnit
    [SmoothOfRelativeDimension d structureMap] :
    constantsToHolomorphicDeRhamPresheafShortComplex structureMap d ⟶
      (constantsToHolomorphicDeRhamSheafShortComplex structureMap d).map
        (TopCat.Sheaf.forget AddCommGrpCat
          (TopCat.of (ComplexPoint X structureMap))) where
  τ₁ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    (constantComplexAddCommGrpPresheaf structureMap)
  τ₂ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    (holomorphicDeRhamPresheaf structureMap d 0)
  τ₃ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    (holomorphicDeRhamPresheaf structureMap d 1)
  comm₁₂ := (toSheafify_naturality
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    (constantsToHolomorphicDeRhamZero structureMap d)).symm
  comm₂₃ := (toSheafify_naturality
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X structureMap)))
    (holomorphicDeRhamDifferential structureMap d 0)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The augmented holomorphic de Rham sheaf complex is exact. Thus the kernel of the exterior
derivative on holomorphic functions is exactly the constant sheaf. -/
lemma constantsToHolomorphicDeRhamSheafShortComplex_exact
    [SmoothOfRelativeDimension d structureMap] :
    (constantsToHolomorphicDeRhamSheafShortComplex structureMap d).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  have hP : ((constantsToHolomorphicDeRhamPresheafShortComplex structureMap d).map
      stalk).Exact :=
    holomorphicStalkExact_of_locallyPrimitive structureMap
      (constantsToHolomorphicDeRhamPresheafShortComplex structureMap d) (by
        intro y U hyU form hform
        change holomorphicFormDifferential structureMap d (.op U) 0 form = 0 at hform
        obtain ⟨V, i, c, hyV, hi⟩ :=
          exists_local_holomorphicForm_eq_constant structureMap d (.op U) y hyU form hform
        exact ⟨V.unop, hyV, i.unop, c, hi.symm⟩) x
  let unit := constantsToHolomorphicDeRhamShortComplexSheafificationUnit structureMap d
  let η := (stalk.mapShortComplex).map unit
  let _ : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (constantComplexAddCommGrpPresheaf structureMap)
  let _ : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf structureMap d 0)
  let _ : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf structureMap d 1)
  let _ : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified inclusion of complex constants into holomorphic functions is a
monomorphism. -/
lemma constantsToHolomorphicDeRhamZeroSheaf_mono
    [SmoothOfRelativeDimension d structureMap] :
    Mono (constantsToHolomorphicDeRhamZeroSheaf structureMap d) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let unit := constantsToHolomorphicDeRhamShortComplexSheafificationUnit structureMap d
  let S := (constantsToHolomorphicDeRhamPresheafShortComplex structureMap d).map stalk
  let T := (constantsToHolomorphicDeRhamSheafShortComplex structureMap d).map
    (TopCat.Sheaf.forget AddCommGrpCat
      (TopCat.of (ComplexPoint X structureMap)) ⋙ stalk)
  let η : S ⟶ T := (stalk.mapShortComplex).map unit
  let _ : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (constantComplexAddCommGrpPresheaf structureMap)
  let _ : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf structureMap d 0)
  let _ : Mono S.f := constantsToHolomorphicDeRhamZero_stalk_mono structureMap d x
  change Mono T.f
  have h : T.f = inv η.τ₁ ≫ S.f ≫ η.τ₂ := by
    rw [← cancel_epi η.τ₁, η.comm₁₂]
    simp
  rw [h]
  infer_instance

/-- The inclusion of constant zero-forms commutes with complex scalar multiplication. -/
lemma constantsToHolomorphicDeRhamZero_scalar
    [SmoothOfRelativeDimension d structureMap] (c : ℂ) :
    constantsToHolomorphicDeRhamZeroSheaf structureMap d ≫
      (let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X structureMap))
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf structureMap d 0 c)) =
    complexScalarSheaf structureMap c ≫
      constantsToHolomorphicDeRhamZeroSheaf structureMap d := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X structureMap))
  change (presheafToSheaf J AddCommGrpCat).map
      (constantsToHolomorphicDeRhamZero structureMap d) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf structureMap d 0 c) =
    (presheafToSheaf J AddCommGrpCat).map
      (complexScalarPresheaf structureMap c) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (constantsToHolomorphicDeRhamZero structureMap d)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  let f := holomorphicFormOfConstant structureMap d U
  change (c • LinearMap.id).toAddMonoidHom.comp f.toAddMonoidHom =
    f.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom ℂ c)
  apply AddMonoidHom.ext
  intro x
  change c • f x = f (c • x)
  exact (f.map_smul c x).symm

/-- The comparison from the constant sheaf complex to the holomorphic de Rham complex. -/
def constantsToHolomorphicDeRhamComplex [SmoothOfRelativeDimension d structureMap] :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)))).obj
        (constantComplexSheaf structureMap) ⟶
      holomorphicDeRhamComplex structureMap d :=
  (CochainComplex.fromSingle₀Equiv (holomorphicDeRhamComplex structureMap d)
    (constantComplexSheaf structureMap)).symm
      ⟨constantsToHolomorphicDeRhamZeroSheaf structureMap d, by
        rw [holomorphicDeRhamComplex_d]
        exact constantsToHolomorphicDeRhamZeroSheaf_comp_differential structureMap d⟩

set_option backward.isDefEq.respectTransparency false in
/-- The holomorphic Poincaré lemma identifies the degree-zero de Rham cohomology sheaf with the
constant sheaf. -/
lemma constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero
    [SmoothOfRelativeDimension d structureMap] :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplex structureMap d) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · exact ⟨constantsToHolomorphicDeRhamSheafShortComplex_exact structureMap d,
      constantsToHolomorphicDeRhamZeroSheaf_mono structureMap d⟩
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- The holomorphic Poincaré lemma makes the constant-to-de Rham comparison a
quasi-isomorphism in every positive degree. -/
lemma constantsToHolomorphicDeRhamComplex_quasiIsoAt_succ
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplex structureMap d) (p + 1) := by
  rw [quasiIsoAt_iff_exactAt _ _
    (CochainComplex.exactAt_succ_single_obj (constantComplexSheaf structureMap) p)]
  exact holomorphicDeRhamComplex_exactAt_succ structureMap d p

/-- The constant sheaf resolves the holomorphic de Rham complex in all natural degrees. -/
instance constantsToHolomorphicDeRhamComplex_quasiIso
    [SmoothOfRelativeDimension d structureMap] :
    QuasiIso (constantsToHolomorphicDeRhamComplex structureMap d) where
  quasiIsoAt p := by
    rcases p with _ | p
    · exact constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero structureMap d
    · exact constantsToHolomorphicDeRhamComplex_quasiIsoAt_succ structureMap d p

/-- The constant-to-de Rham comparison is a quasi-isomorphism in every degree above the complex
dimension. Both sides have zero cohomology there. -/
lemma constantsToHolomorphicDeRhamComplex_quasiIsoAt_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplex structureMap d) p := by
  have hp0 : p ≠ 0 := by lia
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0
  rw [quasiIsoAt_iff_exactAt _ _
    (CochainComplex.exactAt_succ_single_obj (constantComplexSheaf structureMap) q)]
  exact holomorphicDeRhamComplex_exactAt_of_lt structureMap d hp

/-- Scalar multiplication on the constant complex-valued complex concentrated in degree zero. -/
def complexScalarComplex (c : ℂ) :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)))).obj
        (constantComplexSheaf structureMap) ⟶
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)))).obj
        (constantComplexSheaf structureMap) :=
  (CochainComplex.single₀ _).map (complexScalarSheaf structureMap c)

/-- The constant-to-de Rham comparison commutes with complex scalar multiplication. -/
lemma constantsToHolomorphicDeRhamComplex_scalar
    [SmoothOfRelativeDimension d structureMap] (c : ℂ) :
    constantsToHolomorphicDeRhamComplex structureMap d ≫
      scalarHolomorphicDeRhamComplex structureMap d c =
    complexScalarComplex structureMap c ≫
      constantsToHolomorphicDeRhamComplex structureMap d := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · exact constantsToHolomorphicDeRhamZero_scalar structureMap d c
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (constantComplexSheaf structureMap) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

/-- The constant sheaf complex, extended by zero from natural to integer degrees. -/
def constantComplexSheafComplexInt :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) ℤ :=
  ((CochainComplex.single₀
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)))).obj
      (constantComplexSheaf structureMap)).extend ComplexShape.embeddingUpNat

/-- Scalar multiplication on the integer-indexed constant complex-valued complex. -/
def complexScalarComplexInt (c : ℂ) :
    constantComplexSheafComplexInt structureMap ⟶
      constantComplexSheafComplexInt structureMap :=
  HomologicalComplex.extendMap (complexScalarComplex structureMap c)
    ComplexShape.embeddingUpNat

/-- The holomorphic de Rham complex, extended by zero to negative degrees. -/
def holomorphicDeRhamComplexInt [SmoothOfRelativeDimension d structureMap] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) ℤ :=
  (holomorphicDeRhamComplex structureMap d).extend ComplexShape.embeddingUpNat

/-- The integer-indexed holomorphic de Rham complex vanishes in every degree above the complex
dimension. -/
lemma holomorphicDeRhamComplexInt_isZero_X_of_lt
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) (hn : (d : ℤ) < n) :
    IsZero ((holomorphicDeRhamComplexInt structureMap d).X n) := by
  have hn0 : 0 ≤ n := by lia
  let p := n.toNat
  have hp : (p : ℤ) = n := by
    simp [p, Int.toNat_of_nonneg hn0]
  have hdp : d < p := by lia
  exact (holomorphicDeRhamSheaf_isZero_of_lt structureMap d hdp).of_iso
    ((holomorphicDeRhamComplex structureMap d).extendXIso
      ComplexShape.embeddingUpNat hp)

/-- The integer-indexed holomorphic de Rham complex is strictly supported in degrees at most the
complex dimension. -/
noncomputable instance holomorphicDeRhamComplexInt_isStrictlyLE
    [SmoothOfRelativeDimension d structureMap] :
    (holomorphicDeRhamComplexInt structureMap d).IsStrictlySupported
      (ComplexShape.embeddingUpIntLE d) where
  isZero n hn := by
    rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hn
    exact holomorphicDeRhamComplexInt_isZero_X_of_lt structureMap d n hn

/-- Multiplication by a complex scalar on the integer-indexed holomorphic de Rham complex. -/
def scalarHolomorphicDeRhamComplexInt [SmoothOfRelativeDimension d structureMap]
    (c : ℂ) :
    holomorphicDeRhamComplexInt structureMap d ⟶
      holomorphicDeRhamComplexInt structureMap d :=
  HomologicalComplex.extendMap
    (scalarHolomorphicDeRhamComplex structureMap d c) ComplexShape.embeddingUpNat

@[simp] lemma scalarHolomorphicDeRhamComplexInt_zero
    [SmoothOfRelativeDimension d structureMap] :
    scalarHolomorphicDeRhamComplexInt structureMap d 0 = 0 := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_zero, HomologicalComplex.extendMap_zero]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplexInt_one
    [SmoothOfRelativeDimension d structureMap] :
    scalarHolomorphicDeRhamComplexInt structureMap d 1 = 𝟙 _ := by
  unfold scalarHolomorphicDeRhamComplexInt holomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_one]
  exact HomologicalComplex.extendMap_id _ _

@[simp] lemma scalarHolomorphicDeRhamComplexInt_add
    [SmoothOfRelativeDimension d structureMap] (a b : ℂ) :
    scalarHolomorphicDeRhamComplexInt structureMap d (a + b) =
      scalarHolomorphicDeRhamComplexInt structureMap d a +
        scalarHolomorphicDeRhamComplexInt structureMap d b := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_add, HomologicalComplex.extendMap_add]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplexInt_mul
    [SmoothOfRelativeDimension d structureMap] (a b : ℂ) :
    scalarHolomorphicDeRhamComplexInt structureMap d (a * b) =
      scalarHolomorphicDeRhamComplexInt structureMap d b ≫
        scalarHolomorphicDeRhamComplexInt structureMap d a := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_mul, HomologicalComplex.extendMap_comp]
  rfl

/-- The constant-to-de Rham comparison on integer-indexed complexes. -/
def constantsToHolomorphicDeRhamComplexInt [SmoothOfRelativeDimension d structureMap] :
    constantComplexSheafComplexInt structureMap ⟶
      holomorphicDeRhamComplexInt structureMap d :=
  HomologicalComplex.extendMap
    (constantsToHolomorphicDeRhamComplex structureMap d) ComplexShape.embeddingUpNat

/-- Extending by zero gives the holomorphic de Rham quasi-isomorphism in every integer
degree. -/
instance constantsToHolomorphicDeRhamComplexInt_quasiIso
    [SmoothOfRelativeDimension d structureMap] :
    QuasiIso (constantsToHolomorphicDeRhamComplexInt structureMap d) := by
  change QuasiIso (HomologicalComplex.extendMap
    (constantsToHolomorphicDeRhamComplex structureMap d) ComplexShape.embeddingUpNat)
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (constantsToHolomorphicDeRhamComplex structureMap d) ComplexShape.embeddingUpNat).2
      (by infer_instance)

/-- The integer-indexed constant-to-de Rham comparison is a quasi-isomorphism at every
degree. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt structureMap d) n := by
  infer_instance

/-- In a nonnegative degree, extending the constant-to-de Rham comparison from natural to
integer indices does not change whether it is a quasi-isomorphism. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_iff
    [SmoothOfRelativeDimension d structureMap] (p : ℕ) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt structureMap d) (p : ℤ) ↔
      QuasiIsoAt (constantsToHolomorphicDeRhamComplex structureMap d) p := by
  exact HomologicalComplex.quasiIsoAt_extendMap_iff
    (constantsToHolomorphicDeRhamComplex structureMap d)
    ComplexShape.embeddingUpNat rfl

/-- The integer-indexed constant-to-de Rham comparison is automatically a quasi-isomorphism in
negative degrees, since both extended complexes vanish there. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_of_neg
    [SmoothOfRelativeDimension d structureMap] {n : ℤ} (hn : n < 0) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt structureMap d) n := by
  have hnone : ∀ p : ℕ, (p : ℤ) ≠ n := by
    intro p hp
    lia
  rw [quasiIsoAt_iff_exactAt]
  · exact HomologicalComplex.extend_exactAt
      (holomorphicDeRhamComplex structureMap d) ComplexShape.embeddingUpNat n hnone
  · exact HomologicalComplex.extend_exactAt
      ((CochainComplex.single₀
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)))).obj
          (constantComplexSheaf structureMap))
      ComplexShape.embeddingUpNat n hnone

/-- The integer-indexed comparison is a quasi-isomorphism in every nonnegative degree above the
complex dimension. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_of_lt
    [SmoothOfRelativeDimension d structureMap] {p : ℕ} (hp : d < p) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt structureMap d) (p : ℤ) := by
  rw [constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_iff]
  exact constantsToHolomorphicDeRhamComplex_quasiIsoAt_of_lt structureMap d hp

/-- The integer-indexed constant-to-de Rham comparison commutes with complex scalar
multiplication. -/
lemma constantsToHolomorphicDeRhamComplexInt_scalar
    [SmoothOfRelativeDimension d structureMap] (c : ℂ) :
    constantsToHolomorphicDeRhamComplexInt structureMap d ≫
      scalarHolomorphicDeRhamComplexInt structureMap d c =
    complexScalarComplexInt structureMap c ≫
      constantsToHolomorphicDeRhamComplexInt structureMap d := by
  unfold constantsToHolomorphicDeRhamComplexInt
    scalarHolomorphicDeRhamComplexInt complexScalarComplexInt
  change HomologicalComplex.extendMap
      (constantsToHolomorphicDeRhamComplex structureMap d) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (scalarHolomorphicDeRhamComplex structureMap d c) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (complexScalarComplex structureMap c) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (constantsToHolomorphicDeRhamComplex structureMap d) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    constantsToHolomorphicDeRhamComplex_scalar]

end AlgebraicGeometry.ComplexPoint
