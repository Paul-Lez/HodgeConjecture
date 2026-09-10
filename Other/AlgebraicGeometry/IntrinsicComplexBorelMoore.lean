/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.IntrinsicBorelMoore
public import Other.AlgebraicGeometry.ComplexSheafBorelMoore
public import Other.AlgebraicGeometry.SheafBorelMoore
public import Other.AlgebraicGeometry.DerivedSupportRationalForget
public import Other.AlgebraicGeometry.ComplexSheafBorelMooreForget

/-!
# Intrinsic Borel–Moore homology and the constructed complex orientation

The intrinsic group is defined on the analytic space before imposing smoothness.
On a smooth complex space, the already constructed normalized chain-sheaf
orientation identifies it with constant-sheaf hypercohomology in degree `2d-i`.
The comparison is obtained by applying derived Hom to an actual derived
orientation isomorphism; no group-level comparison is an input.

This is the intrinsic smooth-orientation comparison. It is not the comparison
with relative homology of a compactification or the closed-support comparison
for a possibly singular subspace.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))

local instance intrinsicComplexBorelMooreTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance intrinsicComplexBorelMooreDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

/-- The ordinary constant rational coefficient complex on the intrinsic space. -/
def intrinsicBorelMooreRationalConstantComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj
    (singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X)))

/-- The source representing global sections agrees with the source in the
existing hypercohomology API, including the universe-lift comparison. -/
def intrinsicBorelMooreIntegerComplexIso :
    borelMooreIntegerComplex (TopCat.of (ComplexPoint X)) ≅
      constantIntegerSheafComplexInt X :=
  (CochainComplex.singleFunctor _ 0).mapIso
    ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).mapIso
        (AddEquiv.ulift : ULift ℤ ≃+ ℤ).toAddCommGrpIso) ≪≫
    (constantIntegerSheafComplexIntIsoSingle X).symm

/-- The intrinsic construction and the repository'X small-Hom hypercohomology
API compute the same group for the very same coefficient complex. -/
def intrinsicBorelMooreHypercohomologyAddEquiv
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    BorelMooreHypercohomology (TopCat.of (ComplexPoint X)) K n ≃+
      Hypercohomology X K n :=
  (isoHomCongrAddEquiv
    (DerivedCategory.Q.mapIso (intrinsicBorelMooreIntegerComplexIso X))
    (Iso.refl ((DerivedCategory.Q.obj K)⟦n⟧))).trans
      (hypercohomologyAddEquivDerived X K n).symm

/-- The public intrinsic name specializes to hypercohomology of the constructed
chain sheaf in the existing API. No candidate complex is supplied. -/
def intrinsicSheafBorelMooreAddEquivHypercohomology (i : ℤ) :
    IntrinsicSheafBorelMooreHomology X i ≃+
      Hypercohomology X (singularChainSheafCochainComplex ℚ
        (TopCat.of (ComplexPoint X))) (-i) :=
  intrinsicBorelMooreHypercohomologyAddEquiv X _ (-i)

variable (d : ℕ) [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]

/-- The canonical complex orientation, with its target expressed as the
localization of the actual constant-sheaf coefficient complex. -/
def intrinsicComplexChainOrientationIso :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ
      (TopCat.of (ComplexPoint X))) ≅
    (DerivedCategory.Q.obj (intrinsicBorelMooreRationalConstantComplex X))⟦2 * (d : ℤ)⟧ := by
  let e := singularChainSheafDerivedOrientationIso ℚ
    (TopCat.of (ComplexPoint X)) (2 * d)
    (fun m hm z => localHomology_isZero_of_ne X d z m hm)
    (complexOrientationHomologySheafIso X d).symm
  refine e ≪≫ ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (shiftFunctor
      (DerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))))
      (2 * (d : ℤ))).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
          (singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X))))

/-- Intrinsic smooth-ambient duality, from the constructed normalized complex
orientation. Homological degree `i` corresponds to cohomological degree `2d-i`. -/
def intrinsicComplexBorelMooreOrientationIso (i : ℤ) :
    BorelMooreHomology ℚ (TopCat.of (ComplexPoint X)) i ≅
    BorelMooreHypercohomology (TopCat.of (ComplexPoint X))
      (intrinsicBorelMooreRationalConstantComplex X) (2 * (d : ℤ) - i) :=
  borelMooreHypercohomologyIsoOfShiftedIso (TopCat.of (ComplexPoint X))
    ((shiftFunctor _ (-i)).mapIso (intrinsicComplexChainOrientationIso X d) ≪≫
      (shiftFunctorAdd'
        (DerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))))
        (2 * (d : ℤ)) (-i) (2 * (d : ℤ) - i) (by omega)).symm.app _)

/-- Smooth intrinsic Borel–Moore homology agrees with the existing rational
cohomology API, via the constructed complex orientation. -/
def intrinsicComplexBorelMooreAddEquivFieldCohomology (i : ℤ) :
    BorelMooreHomology ℚ (TopCat.of (ComplexPoint X)) i ≃+
      FieldCohomology ℚ X (2 * (d : ℤ) - i) :=
  (intrinsicComplexBorelMooreOrientationIso X d i).addCommGroupIsoToAddEquiv.trans
    ((borelMooreHypercohomologyIsoOfQuasiIso (TopCat.of (ComplexPoint X))
      (constantRationalSheafComplexIntIsoSingleZero X).inv
      (2 * (d : ℤ) - i)).addCommGroupIsoToAddEquiv.trans
        (intrinsicBorelMooreHypercohomologyAddEquiv X _ (2 * (d : ℤ) - i)))

/-- The existing ambient chain-sheaf model with whole-space support and the
intrinsic model are canonically equivalent. Both arrows are constructed from
the same normalized complex orientation and actual global-section comparisons.
This theorem does not assert the corresponding result for a singular support. -/
def intrinsicComplexBorelMooreAddEquivAmbientTop (i : ℤ) :
    BorelMooreHomology ℚ (TopCat.of (ComplexPoint X)) i ≃+
      ComplexAmbientSheafBorelMooreHomology X d ⊤ i :=
  (intrinsicComplexBorelMooreAddEquivFieldCohomology X d i).trans
    (((complexAmbientSheafBorelMooreHomologyIso X d ⊤ i ≪≫
      complexDerivedSupportedCohomologyTopIso X (2 * (d : ℤ) - i)).addCommGroupIsoToAddEquiv.trans
        (derivedRationalCohomologyAddEquiv X (2 * (d : ℤ) - i))).symm)

end AlgebraicGeometry.ComplexPoint
