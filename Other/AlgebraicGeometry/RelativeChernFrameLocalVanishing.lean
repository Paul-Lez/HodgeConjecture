/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernFrameRestriction
public import Other.Algebra.Homology.MappingConeFactorization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-!
# Local vanishing for a frame extending across the open

For V contained in U, the actual relative unit cone of U becomes contractible
under restriction to U. The strict frame-restriction factorization therefore
makes the actual relative cone map for the restricted frame null-homotopic on U.
The existing relative Chern class consequently vanishes under the exact derived
restriction functor, for every comparison datum on V.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
set_option autoImplicit false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The actual single restriction arrow becomes invertible on its own open. -/
instance isIso_restrictToOpen_single_restrictionUnit
    (U : Opens (TopCat.of (ComplexPoint X))) (A : AnalyticAdditiveSheaf X) :
    IsIso (((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map
      ((analyticSingleFunctor X).map (restrictionUnit U A))) := by
  have : IsIso ((restrictToOpen X U).map (restrictionUnit U A)) :=
    TopCat.Sheaf.isIso_sheafPullback_map_toOpenRestrictionPushforward
      (TopCat.of (ComplexPoint X)) U A
  exact (NatIso.isIso_map_iff
    (HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0) (restrictionUnit U A)).mpr
    (by dsimp; infer_instance)

/-- The relative unit cone contracts after restriction to its defining open. -/
def relativeUnitCone_restrict_self_homotopyZero
    (U : Opens (TopCat.of (ComplexPoint X))) :
    Homotopy (𝟙 (((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).obj
      (relativeUnitCone X d U))) 0 :=
  CochainComplex.mappingCone.mapHomologicalComplexConeHomotopyZero (restrictToOpen X U)
    ((analyticSingleFunctor X).map (restrictionUnit U (holomorphicUnitSheaf X d)))

variable (E : HolomorphicUnitExtension X d)
  {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
  (ℓ : E.middle.obj.obj (op U))
  (hℓ : E.projection.hom.app (op U) ℓ =
    (constantIntegerSheaf X).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

/-- An extending frame gives a null-homotopic relative cone map on the larger open. -/
def HolomorphicUnitExtension.relativeConeMap_restrict_homotopyZero :
    Homotopy
      (((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map
        (E.relativeConeMap V (E.middle.obj.map (homOfLE h).op ℓ)
          (E.projection_restrict_lift X h ℓ hℓ))) 0 := by
  let F := (restrictToOpen X U).mapHomologicalComplex (.up ℤ)
  have he := congrArg F.map (E.relativeConeMap_restrict X h ℓ hℓ)
  rw [F.map_comp] at he
  let f := F.map (E.relativeConeMap U ℓ hℓ)
  let g := F.map (relativeUnitConeRestriction X (d := d) h)
  have hh := ((relativeUnitCone_restrict_self_homotopyZero X d U).compLeft f).compRight g
  exact (Homotopy.ofEq he.symm).trans (by simpa using hh)
local instance localFrameAmbientDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
local instance localFrameOpenDerivedCategory (W : Opens (TopCat.of (ComplexPoint X))) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of W)) := HasDerivedCategory.standard _

/-- The actual cone map of the extending frame vanishes after exact derived restriction. -/
lemma HolomorphicUnitExtension.relativeConeMap_restrict_mapDerivedCategory_eq_zero :
    (restrictToOpen X U).mapDerivedCategory.map
      (DerivedCategory.Q.map
        (E.relativeConeMap V (E.middle.obj.map (homOfLE h).op ℓ)
          (E.projection_restrict_lift X h ℓ hℓ))) = 0 := by
  let F := restrictToOpen X U
  have hc := DerivedCategory.Q_map_eq_of_homotopy _
    (E.relativeConeMap_restrict_homotopyZero X d h ℓ hℓ)
  rw [CategoryTheory.Functor.map_zero] at hc
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app (relativeUnitCone X d V))).mp
  have hn := F.mapDerivedCategoryFactors_hom_naturality
    (E.relativeConeMap V (E.middle.obj.map (homOfLE h).op ℓ)
      (E.projection_restrict_lift X h ℓ hℓ))
  exact hn.trans ((congrArg (fun b => F.mapDerivedCategoryFactors.hom.app E.inclusionCone ≫ b)
    hc).trans (comp_zero.trans zero_comp.symm))

/-- The existing relative Chern class of an extending frame vanishes on the larger open. -/
lemma HolomorphicUnitExtension.relativeChernClass_restrict_eq_zero
    (cmp : RelativeChernComparison X d V) :
    (restrictToOpen X U).mapDerivedCategory.map
      (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (E.relativeChernClass V (E.middle.obj.map (homOfLE h).op ℓ)
          (E.projection_restrict_lift X h ℓ hℓ) cmp)) = 0 := by
  rw [E.relativeChernClass_equiv X V _ _ cmp]
  simp only [CategoryTheory.Functor.map_comp,
    E.relativeConeMap_restrict_mapDerivedCategory_eq_zero X d h ℓ hℓ, zero_comp, comp_zero]

end AlgebraicGeometry.ComplexPoint
