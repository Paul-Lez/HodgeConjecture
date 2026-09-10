/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Sections and free abelian sheaves on the analytic variety

A section on an analytic open set determines an actual morphism from the free abelian sheaf
of that open. For the whole variety this free sheaf is identified with the repository's
constant integer sheaf. These are the source comparisons for Mayer-Vietoris transition classes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

/-- The free abelian presheaf represented by an analytic open set. -/
def analyticOpenFreeAbelianPresheaf (U : Opens (TopCat.of (ComplexPoint X s))) :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X s)) :=
  yoneda.obj U ⋙ AddCommGrpCat.free

/-- The corresponding free abelian sheaf. -/
def analyticOpenFreeAbelianSheaf (U : Opens (TopCat.of (ComplexPoint X s))) :
    AnalyticAdditiveSheaf s :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) AddCommGrpCat).obj
    (analyticOpenFreeAbelianPresheaf s U)

/-- A section determines its compatible integer-multiple maps on smaller opens. -/
def analyticSectionPresheafHom (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) (a : F.obj.obj (.op U)) :
    analyticOpenFreeAbelianPresheaf s U ⟶ F.obj where
  app V := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun f : V.unop ⟶ U => F.obj.map f.op a)
  naturality {V W} i := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro f
    change FreeAbelianGroup.lift (fun g : W.unop ⟶ U => F.obj.map g.op a)
      (FreeAbelianGroup.map (fun g : V.unop ⟶ U => i.unop ≫ g) (FreeAbelianGroup.of f)) =
      F.obj.map i (FreeAbelianGroup.lift (fun g : V.unop ⟶ U => F.obj.map g.op a)
        (FreeAbelianGroup.of f))
    simp only [FreeAbelianGroup.map, FreeAbelianGroup.lift_apply_of, Function.comp_apply]
    exact congrArg (fun h => h a) (F.obj.map_comp f.op i)

@[simp]
theorem analyticSectionPresheafHom_zero (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) :
    analyticSectionPresheafHom s F U 0 = 0 := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro f
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of f) = 0
  simp

/-- The sheaf morphism represented by an actual section on an analytic open. -/
def analyticSectionSheafHom (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) (a : F.obj.obj (.op U)) :
    analyticOpenFreeAbelianSheaf s U ⟶ F :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
    (analyticSectionPresheafHom s F U a) F.property⟩

@[simp]
theorem analyticSectionSheafHom_zero (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) : analyticSectionSheafHom s F U 0 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) _ _ F.property
  change toSheafify _ _ ≫ sheafifyLift _ (analyticSectionPresheafHom s F U 0) F.property =
    toSheafify _ _ ≫ 0
  rw [toSheafify_sheafifyLift, analyticSectionPresheafHom_zero, comp_zero]

/-- Evaluating the represented map on the canonical generator recovers the section. -/
theorem analyticSectionSheafHom_generator (F : AnalyticAdditiveSheaf s)
    (U : Opens (TopCat.of (ComplexPoint X s))) (a : F.obj.obj (.op U)) :
    (analyticSectionSheafHom s F U a).hom.app (.op U)
      ((toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s)))
        (analyticOpenFreeAbelianPresheaf s U)).app (.op U)
          (FreeAbelianGroup.of (𝟙 U))) = a := by
  change ((toSheafify _ _ ≫ (analyticSectionSheafHom s F U a).hom).app (.op U)) _ = a
  rw [analyticSectionSheafHom, toSheafify_sheafifyLift]
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of (𝟙 U)) = a
  simp

/-- The free abelian presheaf on the whole analytic space is the constant integer presheaf. -/
def analyticTopFreeAbelianPresheafIso :
    analyticOpenFreeAbelianPresheaf s ⊤ ≅
      (Functor.const (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ).obj (AddCommGrpCat.of ℤ) := by
  let (V : (Opens (TopCat.of (ComplexPoint X s)))ᵒᵖ) : Unique (V.unop ⟶ ⊤) :=
    { default := homOfLE le_top, uniq := fun _ => Subsingleton.elim _ _ }
  refine NatIso.ofComponents (fun V =>
    (FreeAbelianGroup.uniqueEquiv (V.unop ⟶ ⊤)).toAddCommGrpIso) ?_
  intro V W i
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro f
  change FreeAbelianGroup.lift (fun _ : W.unop ⟶ (⊤ : Opens (ComplexPoint X s)) => (1 : ℤ))
      (FreeAbelianGroup.map (fun g : V.unop ⟶ ⊤ => i.unop ≫ g) (FreeAbelianGroup.of f)) =
    FreeAbelianGroup.lift (fun _ : V.unop ⟶ (⊤ : Opens (ComplexPoint X s)) => (1 : ℤ))
      (FreeAbelianGroup.of f)
  simp [FreeAbelianGroup.map]

/-- The free abelian sheaf of the whole analytic variety is its actual constant integer sheaf. -/
def analyticTopFreeAbelianSheafIso :
    analyticOpenFreeAbelianSheaf s ⊤ ≅ constantIntegerSheaf s :=
  (presheafToSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) AddCommGrpCat).mapIso
    (analyticTopFreeAbelianPresheafIso s)

end AlgebraicGeometry.ComplexPoint
