/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.ComplexLocalHomologyVanishing
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexOrientationHomologySheaf
public import HodgeConjecture.Other.AlgebraicTopology.DerivedSheafSupportShift
public import HodgeConjecture.Other.AlgebraicTopology.DerivedSheafSupportNaturality
public import HodgeConjecture.Other.AlgebraicTopology.SingularChainSheafOrientation

/-!
# Concrete ambient sheaf Borel–Moore groups on smooth complex schemes

This module applies the actual right-derived closed-support sections functor to the
sheafification of relative singular chains. Its derived object belongs to `D⁺` by the
proved local homology concentration theorem, although the original chain complex is
not termwise bounded below in cohomological grading.

Thus the ambient group `H^{-i}(RΓ_Z(X, chainSheaf_X))` requires no supplied dualizing
object, support functor, shift compatibility, or bounded model. Homological degree
`i` corresponds to cohomological degree `-i`.

These are ambient groups for a closed support in the specified smooth space. This
module does not assert intrinsic compactification independence or identify these
groups with the existing compactification-relative Borel–Moore groups. The normalized
complex orientation constructs the equivalence with actual derived supported cohomology
below; comparison with the existing support-cone presentation remains a separate theorem.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

noncomputable local instance complexSheafBorelMooreAnalyticTopology :
    TopologicalSpace (ComplexPoint X structureMap) := Point.analyticTopology

local instance complexSheafBorelMooreSheafDerivedCategory : HasDerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) :=
  HasDerivedCategory.standard _

local instance complexSheafBorelMooreGroupsDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable [SmoothOfRelativeDimension d structureMap] [T2Space (ComplexPoint X structureMap)]

/-- Cohomology of the actual chain sheaf is concentrated in degree `-2d`. -/
theorem complexChainSheafCohomology_concentrated (n : ℤ) (hn : n ≠ -(2 * (d : ℤ))) :
    IsZero ((singularChainSheafCochainComplex ℚ
      (TopCat.of (ComplexPoint X structureMap))).homology n) := by
  apply singularChainSheafCochainHomology_concentrated ℚ
    (TopCat.of (ComplexPoint X structureMap)) (2 * d)
      (fun m hm z ↦ localHomology_isZero_of_ne structureMap d z m hm) n
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn

/-- The actual relative-chain sheaf as an object of `D⁺`, using proved local vanishing. -/
def complexChainSheafPlusObject :
    DerivedCategory.Plus
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) :=
  singularChainSheafPlusObject ℚ (TopCat.of (ComplexPoint X structureMap)) (2 * d)
    (fun m hm z ↦ localHomology_isZero_of_ne structureMap d z m hm)

/-- No replacement object is supplied: the underlying derived object is exactly the
localization of the constructed relative-chain sheaf. -/
@[simp]
theorem complexChainSheafPlusObject_obj :
    DerivedCategory.Plus.ι.obj (complexChainSheafPlusObject structureMap d) =
      DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ
        (TopCat.of (ComplexPoint X structureMap))) := rfl

/-- The concrete ambient supported Borel–Moore complex, obtained by right deriving
the actual functor of sections vanishing on the complement of the closed support. -/
def complexAmbientSheafBorelMooreObject (Z : Closeds (ComplexPoint X structureMap)) :
    DerivedCategory.Plus AddCommGrpCat :=
  (TopCat.Sheaf.derivedClosedSupportSections
    (TopCat.of (ComplexPoint X structureMap)) Z).obj
      (complexChainSheafPlusObject structureMap d)

/-- Ambient sheaf Borel–Moore homology in degree `i`, with all objects and derived
support operations constructed. This is not defined as ordinary supported cohomology. -/
def ComplexAmbientSheafBorelMooreHomology
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (-i)).obj
    (complexAmbientSheafBorelMooreObject structureMap d Z)

/-- Enlarge the closed support using the actual derived kernel-inclusion map. -/
def complexAmbientSheafBorelMooreSupportMap
    {Z W : Closeds (ComplexPoint X structureMap)} (h : Z ≤ W) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z i ⟶
      ComplexAmbientSheafBorelMooreHomology structureMap d W i :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (-i)).map
    ((TopCat.Sheaf.derivedClosedSupportSectionsMap
      (TopCat.of (ComplexPoint X structureMap)) h).app
        (complexChainSheafPlusObject structureMap d))

@[simp]
theorem complexAmbientSheafBorelMooreSupportMap_refl
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
      complexAmbientSheafBorelMooreSupportMap structureMap d (le_refl Z) i = 𝟙 _ := by
  unfold complexAmbientSheafBorelMooreSupportMap
  rw [TopCat.Sheaf.derivedClosedSupportSectionsMap_refl]
  exact (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (-i)).map_id _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem complexAmbientSheafBorelMooreSupportMap_comp
    {Z W T : Closeds (ComplexPoint X structureMap)} (h : Z ≤ W) (h' : W ≤ T) (i : ℤ) :
    complexAmbientSheafBorelMooreSupportMap structureMap d h i ≫
        complexAmbientSheafBorelMooreSupportMap structureMap d h' i =
      complexAmbientSheafBorelMooreSupportMap structureMap d (h.trans h') i := by
  unfold complexAmbientSheafBorelMooreSupportMap
  rw [← Functor.map_comp]
  congr 1
  exact NatTrans.congr_app
    (TopCat.Sheaf.derivedClosedSupportSectionsMap_comp
      (TopCat.of (ComplexPoint X structureMap)) h h') _

/-- Forget the specified closed support by enlarging it to the whole ambient space. -/
def complexAmbientSheafBorelMooreForgetSupport
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z i ⟶
      ComplexAmbientSheafBorelMooreHomology structureMap d ⊤ i :=
  complexAmbientSheafBorelMooreSupportMap structureMap d le_top i

/-- The constant rational sheaf in degree zero, as an actual bounded-below derived object. -/
def complexConstantRationalSheafPlusObject :
    DerivedCategory.Plus
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj
    (singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)))

/-- Supported cohomology computed by the actual derived support functor on the constant
rational sheaf. Its comparison to the project's restriction-cone model is a separate theorem. -/
def ComplexDerivedSupportedCohomology
    (Z : Closeds (ComplexPoint X structureMap)) (n : ℤ) : AddCommGrpCat :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X structureMap)) Z).obj
        (complexConstantRationalSheafPlusObject structureMap))

/-- Intermediate orientation transport: an orientation of the actual top homology SHEAF
induces the shifted isomorphism in `D⁺`. Local vanishing and boundedness are proved above;
the sheaf orientation remains an explicit argument to this general transport lemma. -/
def complexChainSheafPlusIsoOfOrientation
    (orientation : singularChainHomologySheaf ℚ
        (TopCat.of (ComplexPoint X structureMap)) (2 * d) ≅
      singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap))) :
    complexChainSheafPlusObject structureMap d ≅
      (complexConstantRationalSheafPlusObject structureMap)⟦2 * (d : ℤ)⟧ := by
  apply DerivedCategory.Plus.ι.preimageIso
  refine singularChainSheafDerivedOrientationIso ℚ
    (TopCat.of (ComplexPoint X structureMap)) (2 * d)
      (fun m hm z ↦ localHomology_isZero_of_ne structureMap d z m hm) orientation ≪≫ ?_
  refine (shiftFunctor
    (DerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))))
      ((2 * d : ℕ) : ℤ)).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app
          (singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)))).symm ≪≫ ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat, complexConstantRationalSheafPlusObject,
    Functor.comp_obj] using
    ((DerivedCategory.Plus.ι.commShiftIso (2 * (d : ℤ))).app
      (complexConstantRationalSheafPlusObject structureMap)).symm

/-- Apply actual derived support to the orientation, using its constructed coherent shifts.
No support functor or shift-compatibility hypothesis is required. -/
def complexAmbientSheafBorelMooreIsoOfOrientation
    (orientation : singularChainHomologySheaf ℚ
        (TopCat.of (ComplexPoint X structureMap)) (2 * d) ≅
      singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)))
    (Z : Closeds (ComplexPoint X structureMap)) :
    complexAmbientSheafBorelMooreObject structureMap d Z ≅
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X structureMap)) Z).obj
          (complexConstantRationalSheafPlusObject structureMap))⟦2 * (d : ℤ)⟧ :=
  (TopCat.Sheaf.derivedClosedSupportSections
    (TopCat.of (ComplexPoint X structureMap)) Z).mapIso
      (complexChainSheafPlusIsoOfOrientation structureMap d orientation) ≪≫
    (TopCat.Sheaf.derivedClosedSupportSectionsShiftIso
      (TopCat.of (ComplexPoint X structureMap)) Z (2 * (d : ℤ))).app _

/-- The actual ambient chain-sheaf group maps isomorphically to supported cohomology
in degree `2d-i`, via the displayed orientation shift. This transport lemma still takes
the top-homology sheaf orientation explicitly; it does not construct that orientation. -/
def complexAmbientSheafBorelMooreHomologyIsoOfOrientation
    (orientation : singularChainHomologySheaf ℚ
        (TopCat.of (ComplexPoint X structureMap)) (2 * d) ≅
      singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)))
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z i ≅
      ComplexDerivedSupportedCohomology structureMap Z (2 * (d : ℤ) - i) := by
  refine (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (-i)).mapIso
    (complexAmbientSheafBorelMooreIsoOfOrientation structureMap d orientation Z) ≪≫ ?_
  refine (DerivedCategory.homologyFunctor AddCommGrpCat (-i)).mapIso
    ((DerivedCategory.Plus.ι.commShiftIso (2 * (d : ℤ))).app _) ≪≫ ?_
  exact ((DerivedCategory.homologyFunctor AddCommGrpCat 0).shiftIso
    (2 * (d : ℤ)) (-i) (2 * (d : ℤ) - i) (by omega)).app _

/-- The cycle-degree specialization, with arithmetic proved rather than supplied.
This is a transport theorem conditional only on the displayed sheaf orientation. -/
def complexAmbientSheafBorelMooreCycleDegreeIsoOfOrientation
    (orientation : singularChainHomologySheaf ℚ
        (TopCat.of (ComplexPoint X structureMap)) (2 * d) ≅
      singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)))
    (Z : Closeds (ComplexPoint X structureMap)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z
        (2 * ((d - p : ℕ) : ℤ)) ≅
      ComplexDerivedSupportedCohomology structureMap Z (2 * (p : ℤ)) :=
  complexAmbientSheafBorelMooreHomologyIsoOfOrientation structureMap d orientation Z
    (2 * ((d - p : ℕ) : ℤ)) ≪≫
      eqToIso (congrArg (ComplexDerivedSupportedCohomology structureMap Z) (by omega))

/-! ### The geometrically normalized route, with no orientation input -/

/-- The canonical unshifted derived orientation of the actual chain sheaf. The
orientation is the inverse of the constructed map sending `1` to the exact complex
local fundamental class; no orientation or comparison equivalence is an argument. -/
def complexChainSheafDerivedSingleOrientationIso :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ
        (TopCat.of (ComplexPoint X structureMap))) ≅
      (DerivedCategory.singleFunctor
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap)))
          (-((2 * d : ℕ) : ℤ))).obj
            (singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap))) :=
  singularChainSheafDerivedSingleOrientationIso ℚ
    (TopCat.of (ComplexPoint X structureMap)) (2 * d)
      (fun m hm z ↦ localHomology_isZero_of_ne structureMap d z m hm)
      (complexOrientationHomologySheafIso structureMap d).symm

/-- The derived orientation induces exactly the geometrically constructed homology-sheaf
orientation, through the canonical grading and localization comparisons. Combined with
`complexOrientationHomologySheafIso_stalk_one`, this fixes its normalization, not merely
its nonvanishing or its rational span. -/
@[reassoc]
theorem complexChainSheafDerivedSingleOrientationIso_homology :
    (DerivedCategory.homologyFunctor _ (-((2 * d : ℕ) : ℤ))).map
        (complexChainSheafDerivedSingleOrientationIso structureMap d).hom ≫
      (DerivedCategory.homologyFunctorFactors _ (-((2 * d : ℕ) : ℤ))).hom.app
        ((HomologicalComplex.single _ (.up ℤ) (-((2 * d : ℕ) : ℤ))).obj
          (singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X structureMap)))) ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) (-((2 * d : ℕ) : ℤ)) _).hom =
      (DerivedCategory.homologyFunctorFactors _ (-((2 * d : ℕ) : ℤ))).hom.app
        (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X structureMap))) ≫
      (singularChainSheafCochainHomologyIso ℚ
        (TopCat.of (ComplexPoint X structureMap)) (2 * d)).hom ≫
      (complexOrientationHomologySheafIso structureMap d).inv :=
  singularChainSheafDerivedSingleOrientationIso_homology ℚ
    (TopCat.of (ComplexPoint X structureMap)) (2 * d)
      (fun m hm z ↦ localHomology_isZero_of_ne structureMap d z m hm)
      (complexOrientationHomologySheafIso structureMap d).symm

/-- The actual chain sheaf is canonically `ℚ_X[2d]` in `D⁺`. Smoothness and
Hausdorffness are the only geometric assumptions; all local concentration and exact
complex-orientation data have been constructed. This does not assert the full
dualizing universal property or any intrinsic closed-embedding comparison. -/
def complexChainSheafPlusOrientationIso :
    complexChainSheafPlusObject structureMap d ≅
      (complexConstantRationalSheafPlusObject structureMap)⟦2 * (d : ℤ)⟧ :=
  complexChainSheafPlusIsoOfOrientation structureMap d
    (complexOrientationHomologySheafIso structureMap d).symm

/-- Apply the actual derived support functor to the constructed complex orientation.
This is the source of smooth-ambient Alexander–Poincaré duality, not a supplied
group-level equivalence. -/
def complexAmbientSheafBorelMooreOrientationIso
    (Z : Closeds (ComplexPoint X structureMap)) :
    complexAmbientSheafBorelMooreObject structureMap d Z ≅
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X structureMap)) Z).obj
          (complexConstantRationalSheafPlusObject structureMap))⟦2 * (d : ℤ)⟧ :=
  complexAmbientSheafBorelMooreIsoOfOrientation structureMap d
    (complexOrientationHomologySheafIso structureMap d).symm Z

/-- Constructed smooth-ambient sheaf duality in every integer degree:
`H_i^BM(Z ⊂ X; ℚ) ≅ H_Z^(2d-i)(X; ℚ)`, where both sides use actual derived support.
The support may be singular. This theorem does not supply its fundamental class or
identify intrinsic homology of that support. -/
def complexAmbientSheafBorelMooreHomologyIso
    (Z : Closeds (ComplexPoint X structureMap)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z i ≅
      ComplexDerivedSupportedCohomology structureMap Z (2 * (d : ℤ) - i) :=
  complexAmbientSheafBorelMooreHomologyIsoOfOrientation structureMap d
    (complexOrientationHomologySheafIso structureMap d).symm Z i

/-- Cycle-degree specialization of the constructed smooth-ambient duality. The
identity `2d - 2(d-p) = 2p` is proved in the transport construction, not assumed. -/
def complexAmbientSheafBorelMooreCycleDegreeIso
    (Z : Closeds (ComplexPoint X structureMap)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology structureMap d Z
        (2 * ((d - p : ℕ) : ℤ)) ≅
      ComplexDerivedSupportedCohomology structureMap Z (2 * (p : ℤ)) :=
  complexAmbientSheafBorelMooreCycleDegreeIsoOfOrientation structureMap d
    (complexOrientationHomologySheafIso structureMap d).symm Z p hp

end AlgebraicGeometry.ComplexPoint
