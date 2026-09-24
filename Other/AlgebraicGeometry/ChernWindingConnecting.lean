/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingRationalCochain
public import Other.AlgebraicTopology.LinearDualConnecting
public import Other.Algebra.Homology.ExtendConnecting
public import Other.AlgebraicTopology.RelativeCochainConeBoundaryComparison

/-!
# The actual relative-cone boundary of rational winding

The additive winding cocycle has precisely the winding-period functional under the
universal-coefficient identification. Its cohomological connecting class is therefore
the relative winding class defined by evaluation on relative homology boundaries.
The result is transported through extension from natural to integer degrees and
through the repository's relative-cone comparison, restricted to boundary classes.

The cone boundary has a positive sign. The separate negation in the supported-injective
comparison is not part of the equivalence studied in this file.
-/

open CategoryTheory Limits AlgebraicTopology.Singular
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace ChernWinding
variable {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)

/-- The additive rational winding cochain as an actual cocycle. -/
def rationalWindingCocycle :
    (singularChains Y).linearDualCochainComplex.cycles 1 :=
  HomologicalComplex.cyclesMk (singularChains Y).linearDualCochainComplex
    (rationalWindingCochain g hg).hom 2 (by simp) (by
    change (singularChains Y).linearDualCochainComplex.d 1 2
      (rationalWindingCochain g hg).hom = 0
    rw [HomologicalComplex.linearDualCochainComplex_d]
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (d_comp_rationalWindingCochain g hg) x)

lemma iCycles_rationalWindingCocycle :
    (singularChains Y).linearDualCochainComplex.iCycles 1 (rationalWindingCocycle g hg) =
      (rationalWindingCochain g hg).hom :=
  HomologicalComplex.i_cyclesMk (singularChains Y).linearDualCochainComplex _ _ _ _

/-- The cohomology class of the additive rational winding cochain. -/
def rationalWindingCohomologyClass :
    (singularChains Y).linearDualCochainComplex.homology 1 :=
  (singularChains Y).linearDualCochainComplex.homologyπ 1 (rationalWindingCocycle g hg)

lemma linearDualHomologyEquiv_rationalWindingCohomologyClass :
    HomologicalComplex.linearDualHomologyEquiv (singularChains Y) 1
      (rationalWindingCohomologyClass g hg) =
      cohomologyEquivDualHomology ℚ Y 1 (windingRationalPeriod g hg) := by
  unfold windingRationalPeriod
  erw [LinearEquiv.apply_symm_apply]
  ext z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((singularChains Y).homologyπ 1)).mp inferInstance z
  unfold rationalWindingCohomologyClass
  rw [HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply,
    iCycles_rationalWindingCocycle]
  exact ConcreteCategory.congr_hom (iCycles_comp_rationalWindingCochain g hg) w

variable {M : Type} [TopologicalSpace M] (W S : Set M)

/-- The actual cohomological connecting class of rational winding is the relative winding
class defined by periods along the relative homology boundary. -/
theorem rationalWindingCohomologyClass_connecting
    (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0)
    (h : HasRationalWindingPeriod W S g hg) :
    (relativeDualCochainShortComplexNat_shortExact ℚ (supportPair W S)).δ 1 2 rfl
      (rationalWindingCohomologyClass g hg) = windingRelativeClass W S h := by
  apply windingRelativeClass_unique W S h
  ext z
  have hp := ShortComplex.linearDualChain_connecting_pairing
    (relativeChainShortComplex ℚ (supportPair W S))
    (relativeChainShortComplex_shortExact ℚ (supportPair W S)) 1
    (rationalWindingCohomologyClass g hg) z
  refine (congrArg (fun q : ℚ => (q : ℂ)) hp).trans ?_
  change ((HomologicalComplex.linearDualHomologyEquiv (singularChains _) 1
    (rationalWindingCohomologyClass g hg)
      ((relativeSingularBoundary (supportPair W S) 1).hom z) : ℚ) : ℂ) = _
  rw [linearDualHomologyEquiv_rationalWindingCohomologyClass]
  exact LinearMap.congr_fun (rationalPeriod_windingRationalPeriod g hg)
    ((relativeSingularBoundary (supportPair W S) 1).hom z)


/-- The winding class in the integer-graded extension of singular cochains. -/
def rationalWindingIntCohomologyClass {Y : TopCat.{0}}
    (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    ((singularChains Y).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).homology (1 : ℤ) :=
  ((singularChains Y).linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 1) (j' := (1 : ℤ)) rfl).inv
      (rationalWindingCohomologyClass g hg)

/-- The repository's actual relative-cone comparison sends the positive cone boundary
of the winding cocycle to the relative winding class. This does not include the later
negation in the supported-injective comparison. -/
theorem relativeCochainConeCohomologyEquiv_boundary_rationalWinding
    (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0)
    (h : HasRationalWindingPeriod W S g hg) :
    relativeCochainConeCohomologyEquiv ℚ (supportPair W S) 2
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr
          (relativeCochainRestrictionInt ℚ (supportPair W S))) 1
        (rationalWindingIntCohomologyClass g hg)) = windingRelativeClass W S h := by
  let P := supportPair W S
  let T := relativeDualCochainShortComplexNat ℚ P
  let a := rationalWindingIntCohomologyClass g hg
  have hb := ConcreteCategory.congr_hom
    (relativeCochainConeHomologyIsoDualRelativeInt_boundary_eq_δ ℚ P 2) a
  change relativeDualCochainCohomologyEquiv ℚ P 2
    ((relativeCochainConeHomologyIsoDualRelativeInt ℚ P 2).hom
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ P)) 1 a)) = _
  change (relativeCochainConeHomologyIsoDualRelativeInt ℚ P 2).hom
      (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ P)) 1 a) =
    (relativeDualCochainShortComplexInt_shortExact ℚ P).δ 1 2 rfl a at hb
  rw [hb]
  have he := HomologicalComplex.extend_connecting ComplexShape.embeddingUpNat T
    (relativeDualCochainShortComplexNat_shortExact ℚ P)
    (relativeDualCochainShortComplexInt_shortExact ℚ P)
    (i := 1) (i' := (1 : ℤ)) (j := 2) (j' := (2 : ℤ)) rfl rfl rfl rfl
  have hea := ConcreteCategory.congr_hom he a
  change (T.X₁.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) rfl).hom
      ((relativeDualCochainShortComplexInt_shortExact ℚ P).δ 1 2 rfl a) =
    (relativeDualCochainShortComplexNat_shortExact ℚ P).δ 1 2 rfl
      ((T.X₃.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) rfl).hom a) at hea
  have ha : (T.X₃.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 1) (j' := (1 : ℤ)) rfl).hom a = rationalWindingCohomologyClass g hg :=
    ConcreteCategory.congr_hom
      (T.X₃.extendHomologyIso ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) rfl).inv_hom_id (rationalWindingCohomologyClass g hg)
  rw [ha] at hea
  change (T.X₁.extendHomologyIso ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) rfl).hom
      ((relativeDualCochainShortComplexInt_shortExact ℚ P).δ 1 2 rfl a) = _
  rw [hea]
  exact rationalWindingCohomologyClass_connecting W S g hg h

end ChernWinding
