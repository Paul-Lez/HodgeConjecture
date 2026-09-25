/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSerreGeneration
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Algebraization from a two-term twist presentation

This file discharges the categorical last step of the Serre-presentation route to GAGA.  If an
analytic module is the cokernel of the analytification of a map between finite sums of algebraic
negative twists, then it is the analytification of the algebraic cokernel of that map.

Producing such a presentation requires analytic Serre generation for the module and for the
kernel of its first presentation, together with algebraization of the resulting relation map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint.ProjectiveTwist

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (P : ProjectiveSpace.Presentation X.hom)

/-- Transport an analytified algebraic map between finite twist sums to the corresponding
analytic twist sums. -/
def analyticRelation {relationDegree relationRank generatorDegree generatorRank : ℕ}
    (f : algebraicSum X P relationDegree relationRank ⟶
      algebraicSum X P generatorDegree generatorRank) :
    analyticSum X d P relationDegree relationRank ⟶
      analyticSum X d P generatorDegree generatorRank :=
  (sumAnalytificationIso X d P relationDegree relationRank).inv ≫
    (moduleAnalytification X d).map f ≫
      (sumAnalytificationIso X d P generatorDegree generatorRank).hom

/-- A two-term presentation of an analytic module in which both terms and the relation map are
analytifications of algebraic finite sums of negative twists. -/
structure AlgebraicTwistPresentation
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d)) where
  relationDegree : ℕ
  relationRank : ℕ
  generatorDegree : ℕ
  generatorRank : ℕ
  relation :
    algebraicSum X P relationDegree relationRank ⟶
      algebraicSum X P generatorDegree generatorRank
  projection : analyticSum X d P generatorDegree generatorRank ⟶ M
  zero : analyticRelation X d P relation ≫ projection = 0
  isCokernel : IsColimit (CokernelCofork.ofπ projection zero)

namespace AlgebraicTwistPresentation

variable {X d P} {M : SheafOfModules.{0} (holomorphicRingSheaf X d)}

/-- The algebraic coherent module selected by a two-term twist presentation. -/
def algebraicModel (Q : AlgebraicTwistPresentation X d P M) : X.left.Modules :=
  cokernel Q.relation

/-- The presentation projection, expressed on the untransported analytification of its
algebraic generator term. -/
def analytifiedProjection (Q : AlgebraicTwistPresentation X d P M) :
    (moduleAnalytification X d).obj
        (algebraicSum X P Q.generatorDegree Q.generatorRank) ⟶ M :=
  (sumAnalytificationIso X d P Q.generatorDegree Q.generatorRank).hom ≫ Q.projection

/-- The analytified algebraic relation is killed by the untransported projection. -/
@[reassoc]
theorem relation_analytifiedProjection (Q : AlgebraicTwistPresentation X d P M) :
    (moduleAnalytification X d).map Q.relation ≫ Q.analytifiedProjection = 0 := by
  rw [analytifiedProjection]
  rw [← cancel_epi
    (sumAnalytificationIso X d P Q.relationDegree Q.relationRank).inv]
  simpa only [analyticRelation, Category.assoc, Iso.inv_hom_id_assoc, zero_comp, comp_zero]
    using Q.zero

/-- The untransported analytified projection is a cokernel of the analytified algebraic
relation. -/
def analytifiedProjectionIsCokernel (Q : AlgebraicTwistPresentation X d P M) :
    IsColimit (CokernelCofork.ofπ Q.analytifiedProjection Q.relation_analytifiedProjection) := by
  apply IsCokernel.ofIso
    (hs := Q.isCokernel)
    (s' := CokernelCofork.ofπ Q.analytifiedProjection Q.relation_analytifiedProjection)
    (eX := (sumAnalytificationIso X d P Q.relationDegree Q.relationRank).symm)
    (eY := (sumAnalytificationIso X d P Q.generatorDegree Q.generatorRank).symm)
    (e := Iso.refl M)
  · change
      (sumAnalytificationIso X d P Q.relationDegree Q.relationRank).inv ≫
          (moduleAnalytification X d).map Q.relation =
        (sumAnalytificationIso X d P Q.relationDegree Q.relationRank).inv ≫
          (moduleAnalytification X d).map Q.relation ≫
            (sumAnalytificationIso X d P Q.generatorDegree Q.generatorRank).hom ≫
              (sumAnalytificationIso X d P Q.generatorDegree Q.generatorRank).inv
    simp
  · simp [analytifiedProjection]

/-- Analytification of the algebraic cokernel is canonically the presented analytic module. -/
def algebraicModelAnalytificationIso (Q : AlgebraicTwistPresentation X d P M) :
    (moduleAnalytification X d).obj Q.algebraicModel ≅ M :=
  PreservesCokernel.iso (moduleAnalytification X d) Q.relation ≪≫
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel ((moduleAnalytification X d).map Q.relation))
      Q.analytifiedProjectionIsCokernel

/-- If the algebraic cokernel of a two-term twist presentation is invertible, the presentation
is already a line-bundle GAGA algebraization witness. -/
theorem algebraizes (Q : AlgebraicTwistPresentation X d P M)
    (hQ : TauCeti.SheafOfModules.IsInvertible Q.algebraicModel) :
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X d).obj L ≅ M) :=
  ⟨Q.algebraicModel, hQ, ⟨Q.algebraicModelAnalytificationIso⟩⟩

end AlgebraicTwistPresentation

end AlgebraicGeometry.ComplexPoint.ProjectiveTwist
