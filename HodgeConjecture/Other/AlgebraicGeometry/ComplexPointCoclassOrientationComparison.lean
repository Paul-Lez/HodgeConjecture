/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.ComplexOrientationHomologySheaf
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentPointPurity

/-!
# Exact point-coclass normalization of the constructed orientation sheaf

The old point coclass evaluates to `1` on exactly the local fundamental class used by
the constructed chain-homology sheaf orientation. Consequently the actual stalk
orientation map followed by the old point-coclass pairing is the identity of `ℚ`.

This is an exact comparison, not a rescaling by one-dimensionality. The point-only
uniqueness theorem states precisely the remaining local test for a proposed class.
This file does **not** assert that the class obtained by derived closed-chain pushforward
passes that test: compatibility of derived sheaf duality and the singular evaluation/cap
pairing, as well as the exact-image supported global comparison, still has to be proved.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

noncomputable local instance pointCoclassOrientationComparisonAnalyticTopology :
    TopologicalSpace (ComplexPoint X structureMap) := Point.analyticTopology

variable [IsProjective structureMap] [SmoothOfRelativeDimension d structureMap]
  (z : ComplexPoint X structureMap)

omit [IsProjective structureMap] in
/-- The old point-local class and the local class used by the sheaf orientation are identical. -/
lemma analyticPointLocalHomologyClass_eq_complexLocalOrientation :
    analyticPointLocalHomologyClass structureMap d z =
      complexLocalOrientation structureMap d z := rfl

/-- The old point coclass evaluates to exactly `1` on the new orientation's local class. -/
@[simp]
lemma analyticPointLocalCoclass_apply_complexLocalOrientation :
    analyticPointLocalCoclass structureMap d z
      (complexLocalOrientation structureMap d z) = 1 :=
  analyticPointLocalCoclass_apply_localClass structureMap d z

/-- The coefficient is preserved exactly, not just up to a nonzero factor. -/
@[simp]
lemma analyticPointLocalCoclass_apply_smul_complexLocalOrientation (q : ℚ) :
    analyticPointLocalCoclass structureMap d z
      (q • complexLocalOrientation structureMap d z) = q := by
  rw [map_smul, analyticPointLocalCoclass_apply_complexLocalOrientation]
  exact mul_one q

/-- In the explicitly point-supported group, evaluation on the exact orientation determines
the coclass. This uniqueness lemma constructs no new general duality equivalence. -/
lemma eq_analyticPointLocalCoclass_iff
    (β : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X structureMap)) {z} (2 * d)) :
    β = analyticPointLocalCoclass structureMap d z ↔
      β (complexLocalOrientation structureMap d z) = 1 := by
  constructor
  · rintro rfl
    exact analyticPointLocalCoclass_apply_complexLocalOrientation structureMap d z
  · intro hβ
    apply LinearMap.ext
    intro c
    obtain ⟨q, rfl⟩ :=
      (Submodule.span_singleton_eq_top_iff ℚ
        (complexLocalOrientation structureMap d z)).mp
          (span_complexLocalOrientation_eq_top structureMap d z) c
    rw [map_smul, hβ, analyticPointLocalCoclass_apply_smul_complexLocalOrientation]
    exact mul_one q

/-- The actual assembled homology-sheaf orientation is dual to the old point coclass
on every stalk, with its coefficient map exactly the identity. -/
@[reassoc]
lemma complexOrientationHomologySheafIso_stalk_pointCoclass :
    (TopCat.Sheaf.constantSheafStalkIso (X := TopCat.of (ComplexPoint X structureMap))
      (AddCommGrpCat.of ℚ) z).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map
        (complexOrientationHomologySheafIso structureMap d).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X structureMap))
        z (2 * d)).hom ≫
      AddCommGrpCat.ofHom
        (analyticPointLocalCoclass structureMap d z).toAddMonoidHom =
      𝟙 (AddCommGrpCat.of ℚ) := by
  erw [complexOrientationHomologySheafIso_stalk_assoc]
  apply ConcreteCategory.hom_ext
  intro q
  exact analyticPointLocalCoclass_apply_smul_complexLocalOrientation structureMap d z q

end AlgebraicGeometry.ComplexPoint
