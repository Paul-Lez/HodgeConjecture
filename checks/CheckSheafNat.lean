import Other.AlgebraicGeometry.SingularCochainMapNaturality

@[expose] noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] {U X : TopCat.{0}} (j : U ⟶ X)

def checkGlobalPushforwardSingularCochainSheafComplexIsoGlobal :
    globalPushforwardSingularCochainSheafComplex R j ≅
      globalSingularCochainSheafComplex R U :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
lemma checkGlobalRawPushforwardToSingularSheaf_transport :
    (globalRawPushforwardSingularCochainComplexIsoGlobal R j).hom ≫
        topOpenToGlobalSingularCochainSheafComplex R U =
      globalRawPushforwardToSingularSheaf R j ≫
        (checkGlobalPushforwardSingularCochainSheafComplexIsoGlobal R j).hom := by
  apply HomologicalComplex.Hom.ext
  funext m
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

def checkOrdinarySingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) (n : ℕ)
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R Y)] :
    OrdinarySingularCohomology R Y n ≃+
      (globalSingularCochainSheafComplex R Y).homology n :=
  (ordinarySingularCohomologyEquivGlobalRaw R Y n).trans
    ((asIso (HomologicalComplex.homologyMap
      (topOpenToGlobalSingularCochainSheafComplex R Y) n)
      ).addCommGroupIsoToAddEquiv)

set_option backward.isDefEq.respectTransparency false in
lemma checkOrdinarySingularCohomologyEquivGlobalSections_naturality
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R X)]
    [QuasiIso (topOpenToGlobalSingularCochainSheafComplex R U)]
    (n : ℕ) (a : OrdinarySingularCohomology R X n) :
    checkOrdinarySingularCohomologyEquivGlobalSections R U n
        (HomologicalComplex.homologyMap
          (HomologicalComplex.linearDualMap
            (((singularChainComplexFunctor (ModuleCat R)).obj
              (ModuleCat.of R R)).map j)) n a) =
      HomologicalComplex.homologyMap
        (globalSingularSheafRestriction R j ≫
          (checkGlobalPushforwardSingularCochainSheafComplexIsoGlobal R j).hom) n
        (checkOrdinarySingularCohomologyEquivGlobalSections R X n a) := by
  change HomologicalComplex.homologyMap
      (topOpenToGlobalSingularCochainSheafComplex R U) n
        (ordinarySingularCohomologyEquivGlobalRaw R U n
          (HomologicalComplex.homologyMap
            (HomologicalComplex.linearDualMap
              (((singularChainComplexFunctor (ModuleCat R)).obj
                (ModuleCat.of R R)).map j)) n a)) = _
  rw [ordinarySingularCohomologyEquivGlobalRaw_naturality]
  rw [← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp]
  rw [Category.assoc,
    checkGlobalRawPushforwardToSingularSheaf_transport]
  rw [← Category.assoc,
    ← globalSingularSheafRestriction_naturality]
  simp [checkOrdinarySingularCohomologyEquivGlobalSections,
    HomologicalComplex.homologyMap_comp]

end AlgebraicTopology.Singular
