/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.LocalSupportVanishing
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FiniteFiltrationVanishing
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport

/-!
# Unique extension across a cycle component's singular boundary

The canonical finite smooth filtration and its layerwise vanishing give the singular
boundary zero supported cohomology below `2(p+1)`, in particular in degrees `2p` and
`2p+1`. The nested-support localization sequence then makes restriction from the full
component support to its smooth-locus ambient open an isomorphism in degree `2p`, whose
inverse is the unique extension operation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- `H^n_{Z_sing,k(ℂ)}(X(ℂ); ℚ) = 0` for `n < 2(p + 1)`, where `Z_sing,k` is the `k`-th stage of
the finite smooth filtration of `Z_sing` (so `Z_sing,0 = Z_sing`). -/
private theorem cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt
    (k : ℕ) (hk : k ≤ cycleComponentSingularFiltrationLength X x)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    -- `H^n_{Z_sing,k(ℂ)}(X(ℂ); ℚ)`, for the `k`-th stage of the singular filtration.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing,k(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing,k(ℂ)`, as a closed subset of `X(ℂ)`.
        (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  let O (j : ℕ) := (cycleComponentSingularAnalyticClosedFiltration X x j).compl
  have hO : Monotone O := fun _ _ hab _ hy hyb ↦
    hy (cycleComponentSingularAnalyticClosedFiltration_antitone X x hab hyb)
  have hN : O (cycleComponentSingularFiltrationLength X x) = ⊤ := by
    dsimp only [O]
    rw [cycleComponentSingularAnalyticClosedFiltration_length]
    ext y
    change (y ∉ (∅ : Set (ComplexPoint X))) ↔ y ∈ Set.univ
    simp
  exact TopCat.Sheaf.finiteNestedSupport_homology_isZero
    (TopCat.of (ComplexPoint X)) O hO (cycleComponentSingularFiltrationLength X x) hN
    (ambientRationalInjectiveComplex X)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (fun j _ => cycleComponentSingularLayerSectionCohomology_isZero_of_lt
      X x hx j n hn) k hk

include hx in
/-- `H^n_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0` for `n < 2(p + 1)`. -/
private theorem cycleComponentSingularBoundarySectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    -- `H^n_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology n) :=
  cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt X x hx
    0 (Nat.zero_le _) n hn

include hx in
/-- `H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`. -/
theorem cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree :
    -- `H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology
      -- Degree `2p`.
      (2 * (p : ℤ))) :=
  cycleComponentSingularBoundarySectionCohomology_isZero_of_lt X x hx _ (by omega)

include hx in
/-- `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ) = 0`. -/
private theorem cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ :
    -- `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ)`.
    IsZero ((((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z_sing(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X
        -- `Z_sing(ℂ)`, as a closed subset of `X(ℂ)`.
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology
      -- Degree `2p + 1`.
      (2 * (p : ℤ) + 1)) :=
  cycleComponentSingularBoundarySectionCohomology_isZero_of_lt X x hx _ (by omega)

/-- Every point of the singular boundary belongs to the full component support. -/
private theorem cycleComponentSingularBoundary_le_support :
    cycleComponentSingularAnalyticClosedFiltration X x 0 ≤ cycleComponentAnalyticClosedSupport X x := by
  intro y hy
  obtain ⟨z, _, hz⟩ := hy
  change y.underlying ∈ closure ({x} : Set X.left)
  rw [← range_cycleComponentι X.left x]
  exact ⟨z, hz⟩

/-- The complement inclusion determining the localization sequence. -/
theorem cycleComponentSupportComplement_le_smoothAmbientOpen :
    (cycleComponentAnalyticClosedSupport X x).compl ≤ cycleComponentSmoothSupportAmbientOpen X x :=
  fun _ hy hyS ↦ hy (cycleComponentSingularBoundary_le_support X x hyS)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Let `I^•` be the chosen injective resolution of `ℚ` on `X(ℂ)`.
This restricts sections of its subsheaves supported in `Z(ℂ)` from all of `X(ℂ)` to `X(ℂ) \
Z_sing(ℂ)`, degree by degree. -/
def cycleComponentSupportSectionRestriction :
    -- Restriction `RΓ_{Z(ℂ)}(X(ℂ)) → RΓ_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ))`.
    ((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Global sections.
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      -- `RΓ_{Z(ℂ)}(ℚ)`.
      (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) ⟶
    ((TopCat.Sheaf.supportEvaluation
      -- `X(ℂ)`.
      (TopCat.of (ComplexPoint X))
      -- Sections over the open `X(ℂ) \ Z_sing(ℂ)`.
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex ℤᵘᵖ).obj
        -- `RΓ_{Z(ℂ)}(ℚ)`.
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) :=
  TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) (homOfLE le_top)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hx in
/-- Restriction `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) → H^{2p}_{Z(ℂ)}(X(ℂ) \ Z_sing(ℂ); ℚ)` is an isomorphism:
in the localization sequence for `Z_sing(ℂ) ⊆ Z(ℂ)`, the neighbouring terms
`H^{2p}_{Z_sing(ℂ)}(X(ℂ); ℚ)` and `H^{2p+1}_{Z_sing(ℂ)}(X(ℂ); ℚ)` vanish. -/
theorem cycleComponentSupportSectionRestriction_homology_isIso :
    IsIso (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ))) := by
  let T := TopCat.of (ComplexPoint X)
  let h := cycleComponentSupportComplement_le_smoothAmbientOpen X x
  let K := ambientRationalInjectiveComplex X
  let S := TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex T h ⊤ K
  let := TopCat.Sheaf.nestedSupportRestriction_homologyMap_isIso_of_vanishing T h ⊤ K
    (2 * (p : ℤ))
    (cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree X x hx)
    (cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ X x hx)
  have he : HomologicalComplex.homologyMap S.g (2 * (p : ℤ)) ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso T h K).hom (2 * (p : ℤ)) =
    HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f (2 * (p : ℤ)))
      (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso_g T h K)
  rw [← he]
  infer_instance

include hx in
/-- The singular-boundary supported Ext groups vanish below degree `2(p + 1)`. -/
theorem cycleComponentSingularBoundaryRelH_isZero_of_lt (n : ℕ)
    (hn : (n : ℤ) < 2 * ((p : ℤ) + 1)) :
    IsZero (AddCommGrpCat.of
      (CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        n
        (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤
          (⊤ : Opens (TopCat.of (ComplexPoint X))) from le_top)))) := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentSingularAnalyticClosedFiltration X x 0
  let e := rationalSupportAddEquivSupportedInjectiveHomology X Z n
  let hcomplex : IsZero ((((TopCat.Sheaf.supportEvaluation T ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X Z)).homology (n : ℤ)) := by
    simpa [Z] using cycleComponentSingularBoundarySectionCohomology_isZero_of_lt
      X x hx (n : ℤ) hn
  let : Subsingleton ((((TopCat.Sheaf.supportEvaluation T ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X Z)).homology (n : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero hcomplex
  let : Subsingleton (H_[cycleComponentSingularAnalyticClosedFiltration X x 0]^n(X; ℚ)) :=
    e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

set_option maxHeartbeats 800000 in
include hx in
/-- `H_[Z]^{2p}(X; ℚ) ≃ relH ℚ (2p) (Z.compl ≤ U)`, where `U` is the smooth ambient open. -/
def cycleComponentSupportExtensionIso :
    H_[cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ) ≃+
      CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        (2 * p)
        (homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)) := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let U := cycleComponentSmoothSupportAmbientOpen X x
  let f : Z.compl ⟶ U := homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)
  let g : U ⟶ ⊤ := homOfLE le_top
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let n : ℕ := 2 * p
  simpa [f, g] using CategoryTheory.Sheaf.relH.restrictEquivOfIsZero F f g n
    (by
      exact cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx n (by omega))
    (by
      exact cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx (n + 1) (by omega))

end AlgebraicGeometry.ComplexPoint
