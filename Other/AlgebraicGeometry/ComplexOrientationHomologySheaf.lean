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

public import Other.AlgebraicGeometry.ComplexLocalOrientationNeighborhood
public import Other.AlgebraicTopology.HomologySheafSection
public import Other.AlgebraicTopology.SheafMapOfLocallyRepresentableStalks
public import Other.AlgebraicTopology.SingularChainSheafOrientation

/-!
# The actual normalized complex orientation of the singular homology sheaf

The exact complex local classes are represented by genuine relative homology classes on
open neighborhoods. The canonical relative-homology-to-sheaf-section map proves their
local representability in the actual homology sheaf. Unique sheaf gluing constructs the
map from the constant rational sheaf, and the previously proved normalized local
generator theorem proves it is an isomorphism. No orientation or local-representability
datum is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

noncomputable local instance complexOrientationHomologySheafAnalyticTopology :
    TopologicalSpace (ComplexPoint X structureMap) := Point.analyticTopology

variable [SmoothOfRelativeDimension d structureMap]
  [T2Space (ComplexPoint X structureMap)]

/-- Scalar multiples of the exact normalized local orientation, viewed in the actual
homology-sheaf stalk through its canonical local-homology comparison. -/
def complexOrientationHomologyStalkMap (x : ComplexPoint X structureMap) :
    AddCommGrpCat.of ℚ ⟶
      (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X structureMap)) (2 * d)).presheaf.stalk x :=
  AddCommGrpCat.ofHom
    ((LinearMap.toSpanSingleton ℚ _ (complexLocalOrientation structureMap d x)).toAddMonoidHom) ≫
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X structureMap)) x (2 * d)).inv

/-- Local representability is proved using the actual geometric neighborhood class,
not assumed as an orientation-sheaf field. -/
theorem complexOrientationHomologyStalkMap_locallyRepresentable :
    ∀ (q : ℚ) (x : ComplexPoint X structureMap),
      ∃ (U : Opens (ComplexPoint X structureMap)) (_ : x ∈ U)
        (s : (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X structureMap))
          (2 * d)).presheaf.obj (op U)),
        ∀ (y : ComplexPoint X structureMap) (hy : y ∈ U),
          (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X structureMap))
            (2 * d)).presheaf.germ U y hy s =
              complexOrientationHomologyStalkMap structureMap d y q := by
  intro q x
  let U := complexLocalOrientationNeighborhood structureMap d x
  let c := complexLocalOrientationNeighborhoodClass structureMap d x
  refine ⟨U, mem_complexLocalOrientationNeighborhood structureMap d x,
    relativeHomologyToHomologySheafSection ℚ (TopCat.of (ComplexPoint X structureMap))
      U (2 * d) (q • c), ?_⟩
  intro y hy
  apply ((ConcreteCategory.isIso_iff_bijective
    (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X structureMap))
      y (2 * d)).hom).mp inferInstance).injective
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ
      (TopCat.of (ComplexPoint X structureMap)) U y hy (2 * d)) (q • c)
  simp only [ConcreteCategory.comp_apply] at hgerm
  erw [hgerm]
  change relativeHomologyMap ℚ (2 * d) (supportInclusionPairMap _ _) (q • c) =
    (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X structureMap))
      y (2 * d)).hom ((singularChainHomologySheafStalkIso ℚ
        (TopCat.of (ComplexPoint X structureMap)) y (2 * d)).inv
          (q • complexLocalOrientation structureMap d y))
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  change relativeHomologyMap ℚ (2 * d) (supportInclusionPairMap _ _) (q • c) =
    q • complexLocalOrientation structureMap d y
  rw [map_smul]
  exact congrArg (q • ·) (complexLocalOrientationNeighborhoodClass_restrict structureMap d x y hy)

/-- Each stalk map is an isomorphism by the already constructed, exactly normalized
local generator theorem. -/
theorem complexOrientationHomologyStalkMap_isIso (x : ComplexPoint X structureMap) :
    IsIso (complexOrientationHomologyStalkMap structureMap d x) := by
  have hne : complexLocalOrientation structureMap d x ≠ 0 :=
    localClassOfChart_ne_zero d (localChart structureMap d x) x
      (mem_localChart_source structureMap d x)
  have hbij : Function.Bijective (LinearMap.toSpanSingleton ℚ _
      (complexLocalOrientation structureMap d x)) := by
    constructor
    · exact smul_left_injective ℚ hne
    · intro a
      have ha : a ∈ Submodule.span ℚ {complexLocalOrientation structureMap d x} := by
        rw [span_complexLocalOrientation_eq_top]
        exact Submodule.mem_top
      exact Submodule.mem_span_singleton.mp ha
  let : IsIso (AddCommGrpCat.ofHom
      ((LinearMap.toSpanSingleton ℚ _ (complexLocalOrientation structureMap d x)).toAddMonoidHom)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  unfold complexOrientationHomologyStalkMap
  infer_instance

/-- The actual sheaf map obtained by gluing the geometric neighborhood orientations. -/
def constantToComplexOrientationHomologySheaf :
    singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)) ⟶
      singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X structureMap)) (2 * d) :=
  TopCat.Sheaf.constantSheafMapOfLocallyRepresentable _ (AddCommGrpCat.of ℚ)
    (complexOrientationHomologyStalkMap structureMap d)
    (complexOrientationHomologyStalkMap_locallyRepresentable structureMap d)

/-- The constructed normalized orientation is an isomorphism of actual sheaves. -/
def complexOrientationHomologySheafIso :
    singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)) ≅
      singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X structureMap)) (2 * d) := by
  letI : IsIso (constantToComplexOrientationHomologySheaf structureMap d) := by
    unfold constantToComplexOrientationHomologySheaf
    exact TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_isIso
      (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X structureMap)) (2 * d))
      (AddCommGrpCat.of ℚ)
      (complexOrientationHomologyStalkMap structureMap d)
      (complexOrientationHomologyStalkMap_locallyRepresentable structureMap d)
      (complexOrientationHomologyStalkMap_isIso structureMap d)
  exact asIso (constantToComplexOrientationHomologySheaf structureMap d)

/-- On every stalk the assembled sheaf isomorphism is scalar multiplication by the
exact complex orientation, through the canonical constant and local-homology maps. -/
@[reassoc]
theorem complexOrientationHomologySheafIso_stalk (x : ComplexPoint X structureMap) :
    (TopCat.Sheaf.constantSheafStalkIso (X := TopCat.of (ComplexPoint X structureMap))
      (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (complexOrientationHomologySheafIso structureMap d).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X structureMap))
        x (2 * d)).hom =
      AddCommGrpCat.ofHom
        ((LinearMap.toSpanSingleton ℚ _ (complexLocalOrientation structureMap d x)).toAddMonoidHom) := by
  change _ ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (constantToComplexOrientationHomologySheaf structureMap d).hom ≫ _ = _
  unfold constantToComplexOrientationHomologySheaf
  rw [← Category.assoc]
  erw [TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_stalk]
  unfold complexOrientationHomologyStalkMap
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In particular the isomorphism sends the germ of the constant section `1` to
the exact normalized complex local fundamental class. -/
theorem complexOrientationHomologySheafIso_stalk_one (x : ComplexPoint X structureMap) :
    ((TopCat.Sheaf.constantSheafStalkIso (X := TopCat.of (ComplexPoint X structureMap))
      (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (complexOrientationHomologySheafIso structureMap d).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X structureMap))
        x (2 * d)).hom) 1 = complexLocalOrientation structureMap d x := by
  rw [complexOrientationHomologySheafIso_stalk]
  exact LinearMap.toSpanSingleton_apply_one ℚ _ (complexLocalOrientation structureMap d x)

end AlgebraicGeometry.ComplexPoint
