/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCochainCoefficientBaseChange

/-!
# Naturality of rational-to-complex singular (co)homology

The chain-level rational-to-complex map is natural in the space.  Here that square is
passed through homology, including the canonical comparison between homology after
restriction of scalars and restriction of scalars after homology.  Dualizing gives
naturality of rational-to-complex singular cohomology in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular

local instance coefficientNaturalityRatModule (X : TopCat) (n : ℕ) :
    Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance coefficientNaturalityRatScalarTower (X : TopCat) (n : ℕ) :
    IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- The chain map induced by a continuous map, with rational coefficients. -/
def rationalSingularChainMap {X Y : TopCat} (f : X ⟶ Y) : QChains X ⟶ QChains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)

/-- The chain map induced by a continuous map, with complex coefficients. -/
def complexSingularChainMap {X Y : TopCat} (f : X ⟶ Y) : CChains X ⟶ CChains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℂ ℂ)

/-- The complex singular chain map regarded as a map of rational chain complexes. -/
def restrictedComplexSingularChainMap {X Y : TopCat} (f : X ⟶ Y) :
    RestrictedCChains X ⟶ RestrictedCChains Y :=
  ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (complexSingularChainMap f)

/-- Rational-to-complex coefficient extension is a natural transformation on singular
chain complexes. -/
theorem qToCChainMap_naturality {X Y : TopCat} (f : X ⟶ Y) :
    qToCChainMap X ≫ restrictedComplexSingularChainMap f =
      rationalSingularChainMap f ≫ qToCChainMap Y := by
  ext n
  exact ConcreteCategory.congr_hom (qToCChainGroup_naturality f n) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical restriction-of-scalars comparison for homology is natural in the
chain complex. -/
theorem restrictedCChainsHomologyIso_naturality
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (restrictedComplexSingularChainMap f) n ≫
        (restrictedCChainsHomologyIso Y n).hom =
      (restrictedCChainsHomologyIso X n).hom ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (HomologicalComplex.homologyMap (complexSingularChainMap f) n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℂ)
      (ComplexShape.down ℕ) n).map (complexSingularChainMap f))
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of rational-to-complex coefficient extension as a morphism between
the selected singular homology objects. -/
theorem qToCHomology_naturality_hom
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ModuleCat.ofHom (qToCHomology X n) ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          (HomologicalComplex.homologyMap (complexSingularChainMap f) n) =
      HomologicalComplex.homologyMap (rationalSingularChainMap f) n ≫
        ModuleCat.ofHom (qToCHomology Y n) := by
  change (HomologicalComplex.homologyMap (qToCChainMap X) n ≫
      (restrictedCChainsHomologyIso X n).hom) ≫ _ =
    _ ≫ (HomologicalComplex.homologyMap (qToCChainMap Y) n ≫
      (restrictedCChainsHomologyIso Y n).hom)
  rw [Category.assoc, ← restrictedCChainsHomologyIso_naturality f n]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp]
  rw [qToCChainMap_naturality f]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational-to-complex coefficient extension in singular homology commutes with every
continuous map, in every degree. -/
theorem qToCHomology_naturality
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (z : Homology ℚ X n) :
    homologyMap ℂ n f (qToCHomology X n z) =
      qToCHomology Y n (homologyMap ℚ n f z) := by
  exact ConcreteCategory.congr_hom (qToCHomology_naturality_hom f n) z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational-to-complex coefficient extension in singular cohomology commutes with
pullback along every continuous map, in every degree. -/
theorem rationalToComplexCohomologyMap_naturality
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (beta : Cohomology ℚ Y n) :
    rationalToComplexCohomologyMap X n (cohomologyMap ℚ n f beta) =
      cohomologyMap ℂ n f (rationalToComplexCohomologyMap Y n beta) := by
  apply LinearMap.ext
  intro w
  apply (qToCHomology_isBaseChange X n).inductionOn w
    (fun w =>
      rationalToComplexCohomologyMap X n (cohomologyMap ℚ n f beta) w =
        cohomologyMap ℂ n f (rationalToComplexCohomologyMap Y n beta) w)
  · simp
  · intro z
    rw [cohomologyMap_apply, qToCHomology_naturality]
    exact ((qToCHomology_isBaseChange X n).toDual_comp_apply
      (cohomologyMap ℚ n f beta) z).trans
        ((qToCHomology_isBaseChange Y n).toDual_comp_apply beta
          (homologyMap ℚ n f z)).symm
  · intro a z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

end AlgebraicTopology.Singular
