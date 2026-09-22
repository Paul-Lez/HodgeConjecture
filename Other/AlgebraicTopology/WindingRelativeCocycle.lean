/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.WindingCochainRational
public import HodgeConjecture.Definitions.AlgebraicTopology.RelativeCochainConeNaturality
public import HodgeConjecture.Lemmas.AlgebraicTopology.LinearDualConnecting
public import HodgeConjecture.Lemmas.AlgebraicTopology.RelativeCochainConeRawBoundary
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# A literal relative cocycle from winding

The winding index is not merely used through its induced functional on homology.  This file puts
the actual integer-valued singular `1`-cochain into the mapping-cone model for a pair.  The
resulting degree-two relative cocycle is the pair `(0, windingIndex)`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology.Singular

namespace ChernWinding

variable {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)

/-- The winding index, regarded as an element of the degree-one rational singular-cochain
module. -/
def windingIntegerCochainElement :
    ((singularChains Y).linearDualCochainComplex).X 1 :=
  (windingIntegerCochain g hg).hom

/-- The literal winding-index cochain is closed in the singular cochain complex. -/
lemma windingIntegerCochainElement_closed :
    ((singularChains Y).linearDualCochainComplex).d 1 2
      (windingIntegerCochainElement g hg) = 0 := by
  change ((singularChains Y).d 2 1 ≫ windingIntegerCochain g hg).hom = 0
  rw [d_comp_windingIntegerCochain]
  rfl

variable {X : TopPair.{0}} (g : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0)

/-- The winding-index cochain, with the pair's subspace-chain complex written explicitly. -/
def pairWindingIntegerCochainElement :
    (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).X 1 :=
  (windingIntegerCochain g hg).hom

def pairWindingIntegerCochainHom :
    ModuleCat.of ℚ ℚ ⟶
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).X 1 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _
    (pairWindingIntegerCochainElement (X := X) g hg))

lemma pairWindingIntegerCochainElement_closed :
    (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).d 1 2
      (pairWindingIntegerCochainElement (X := X) g hg) = 0 := by
  change ((singularChains X.snd).d 2 1 ≫ windingIntegerCochain g hg).hom = 0
  rw [d_comp_windingIntegerCochain]
  rfl

lemma pairWindingIntegerCochainHom_closed :
    pairWindingIntegerCochainHom (X := X) g hg ≫
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).d 1 2 = 0 := by
  ext
  change (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).d 1 2
    (LinearMap.toSpanSingleton ℚ _
      (pairWindingIntegerCochainElement (X := X) g hg) 1) = 0
  simp only [LinearMap.toSpanSingleton_apply]
  simpa using pairWindingIntegerCochainElement_closed (X := X) g hg

/-- The winding cochain after extending the nonnegative singular cochain complex to all integer
degrees. -/
def extendedWindingIntegerCochainElement :
    (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).X (ComplexShape.embeddingUpNat.f 1) :=
  (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat rfl).inv
      ((pairWindingIntegerCochainHom (X := X) g hg).hom 1)

def extendedWindingIntegerCochainHom :
    ModuleCat.of ℚ ℚ ⟶
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).X (ComplexShape.embeddingUpNat.f 1) :=
  pairWindingIntegerCochainHom (X := X) g hg ≫
    (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat rfl).inv

lemma extendedWindingIntegerCochainHom_closed :
    extendedWindingIntegerCochainHom (X := X) g hg ≫
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 1)
          (ComplexShape.embeddingUpNat.f 2) = 0 := by
  dsimp [extendedWindingIntegerCochainHom]
  rw [Category.assoc]
  exact (HomologicalComplex.extend.comp_d_eq_zero_iff
    ((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex
    ComplexShape.embeddingUpNat (j := 1) (k := 2) (j' := (1 : ℤ)) (k' := 2)
      rfl (by simp) (by simp)
      (pairWindingIntegerCochainHom (X := X) g hg)).mp
        (pairWindingIntegerCochainHom_closed (X := X) g hg)

/-- Extending by zero preserves closedness of the winding cochain. -/
lemma extendedWindingIntegerCochainElement_closed :
    ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 1)
        (ComplexShape.embeddingUpNat.f 2))
      (extendedWindingIntegerCochainElement (X := X) (g := g) hg) = 0 := by
  change ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 1)
        (ComplexShape.embeddingUpNat.f 2)).hom
      ((extendedWindingIntegerCochainHom (X := X) g hg).hom 1) = 0
  simpa using congrArg (fun f => f.hom 1)
    (extendedWindingIntegerCochainHom_closed (X := X) g hg)

/-- The literal winding cochain, regarded as a degree-one cycle in the subspace cochain
complex. -/
def pairWindingIntegerCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).cycles 1 :=
  (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).liftCycles
    (pairWindingIntegerCochainHom (X := X) g hg) 2 (by simp)
    (pairWindingIntegerCochainHom_closed (X := X) g hg)

/-- The same literal winding cochain after extension to the integer-indexed complex. -/
def extendedWindingIntegerCocycle :
    ModuleCat.of ℚ ℚ ⟶
      ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).cycles (ComplexShape.embeddingUpNat.f 1)) :=
  (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
    ComplexShape.embeddingUpNat).liftCycles
      (extendedWindingIntegerCochainHom (X := X) g hg)
      (ComplexShape.embeddingUpNat.f 2) (by simp)
      (extendedWindingIntegerCochainHom_closed (X := X) g hg)

/-- The extended literal cocycle is exactly the original cocycle under the extension cycles
isomorphism. -/
lemma extendedWindingIntegerCocycle_transport :
    extendedWindingIntegerCocycle (X := X) g hg ≫
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extendCyclesIso
        ComplexShape.embeddingUpNat (j := 1) rfl).hom =
    pairWindingIntegerCocycle (X := X) g hg := by
  let K := ((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex
  change extendedWindingIntegerCocycle (X := X) g hg ≫
      (K.extendCyclesIso ComplexShape.embeddingUpNat (j := 1) rfl).hom =
    pairWindingIntegerCocycle (X := X) g hg
  rw [← cancel_mono (K.iCycles 1)]
  rw [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles]
  dsimp [extendedWindingIntegerCocycle]
  rw [← Category.assoc, HomologicalComplex.liftCycles_i]
  dsimp [pairWindingIntegerCocycle, extendedWindingIntegerCochainHom]
  rw [HomologicalComplex.liftCycles_i]
  simp [K]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Applying universal coefficients to the literal winding cocycle gives exactly the
integer winding period.  This is an evaluation calculation on actual cycles, so it does not
use a cycle-class or Chern-class comparison. -/
theorem pairWindingIntegerCocycle_class_eq_windingRationalPeriod :
    HomologicalComplex.linearDualHomologyEquiv ((chainPairFunctor ℚ).obj X).left 1
      ((pairWindingIntegerCocycle (X := X) g hg ≫
        (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).homologyπ 1).hom 1) =
      windingRationalPeriod g hg := by
  change HomologicalComplex.linearDualHomologyEquiv (singularChains X.snd) 1
    ((pairWindingIntegerCocycle (X := X) g hg ≫
      ((singularChains X.snd).linearDualCochainComplex).homologyπ 1).hom 1) =
    windingRationalPeriod g hg
  apply LinearMap.ext
  intro z
  let L := singularChains X.snd
  let S := L.sc 1
  obtain ⟨x, rfl⟩ := S.moduleCatHomologyClass_surjective z
  let K := L.linearDualCochainComplex
  let T := K.sc 1
  let phi : LinearMap.ker (T.g.hom) :=
    T.moduleCatCyclesIso.hom ((pairWindingIntegerCocycle (X := X) g hg).hom 1)
  have hphi_eq : T.moduleCatCyclesIso.inv.hom phi =
      (pairWindingIntegerCocycle (X := X) g hg).hom 1 := by
    exact T.moduleCatCyclesIso.toLinearEquiv.symm_apply_apply _
  have hclass :
      (pairWindingIntegerCocycle (X := X) g hg ≫ K.homologyπ 1).hom 1 =
        T.moduleCatHomologyClass phi := by
    change (K.homologyπ 1).hom ((pairWindingIntegerCocycle (X := X) g hg).hom 1) = _
    rw [← hphi_eq]
    change T.homologyπ (T.moduleCatCyclesIso.inv phi) = T.moduleCatHomologyClass phi
    have hπ := ConcreteCategory.congr_hom (ShortComplex.moduleCatCyclesIso_inv_π T) phi
    change T.homologyπ (T.moduleCatCyclesIso.inv phi) =
      (T.moduleCatLeftHomologyData.π ≫ T.moduleCatHomologyIso.inv).hom phi at hπ
    rw [hπ]
    rfl
  have hphi_value :
      (ShortComplex.moduleCatCycleMap
        (HomologicalComplex.linearDualCochainComplexScIso L 1).hom phi).1 =
      (windingIntegerCochain g hg).hom := by
    change phi.1 = (windingIntegerCochain g hg).hom
    have h := ConcreteCategory.congr_hom (ShortComplex.moduleCatCyclesIso_hom_i T)
      ((pairWindingIntegerCocycle (X := X) g hg).hom 1)
    change phi.1 = T.iCycles.hom
      ((pairWindingIntegerCocycle (X := X) g hg).hom 1) at h
    rw [h]
    change ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.iCycles 1).hom
      ((pairWindingIntegerCocycle (X := X) g hg).hom 1)) = _
    have h' := ConcreteCategory.congr_hom
      (HomologicalComplex.liftCycles_i
        (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex)
        (pairWindingIntegerCochainHom (X := X) g hg) 2 (by simp)
        (pairWindingIntegerCochainHom_closed (X := X) g hg)) 1
    change ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.iCycles 1).hom
      ((pairWindingIntegerCocycle (X := X) g hg).hom 1)) =
      (pairWindingIntegerCochainHom (X := X) g hg).hom 1 at h'
    rw [h']
    dsimp [pairWindingIntegerCochainHom, pairWindingIntegerCochainElement]
    simp
  have hxclass :
      (L.homologyπ 1).hom (S.moduleCatCyclesIso.inv x) = S.moduleCatHomologyClass x := by
    change S.homologyπ (S.moduleCatCyclesIso.inv x) = S.moduleCatHomologyClass x
    have hπ := ConcreteCategory.congr_hom (ShortComplex.moduleCatCyclesIso_inv_π S) x
    change S.homologyπ (S.moduleCatCyclesIso.inv x) =
      (S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv).hom x at hπ
    rw [hπ]
    rfl
  have hxvalue : (L.iCycles 1).hom (S.moduleCatCyclesIso.inv x) = x.1 := by
    have h := ConcreteCategory.congr_hom
      (ShortComplex.moduleCatCyclesIso_inv_iCycles S) x
    change (L.iCycles 1).hom (S.moduleCatCyclesIso.inv x) = x.1 at h
    exact h
  have hperiod :
      (windingRationalPeriodHom g hg).hom (S.moduleCatHomologyClass x) =
        (windingIntegerCochain g hg).hom x.1 := by
    rw [← hxclass]
    have h := ConcreteCategory.congr_hom
      (homologyπ_comp_windingRationalPeriodHom g hg) (S.moduleCatCyclesIso.inv x)
    change (windingRationalPeriodHom g hg).hom
      ((L.homologyπ 1).hom (S.moduleCatCyclesIso.inv x)) =
        (windingIntegerCochain g hg).hom
          ((L.iCycles 1).hom (S.moduleCatCyclesIso.inv x)) at h
    rw [h, hxvalue]
  change HomologicalComplex.linearDualHomologyEquiv L 1
    ((pairWindingIntegerCocycle (X := X) g hg ≫ K.homologyπ 1).hom 1)
    (S.moduleCatHomologyClass x) =
      (windingRationalPeriodHom g hg).hom (S.moduleCatHomologyClass x)
  rw [hclass]
  rw [HomologicalComplex.linearDualHomologyEquiv_moduleCatHomologyClass_apply L 1 phi x]
  rw [hphi_value]
  exact hperiod.symm

/-- The degree-two relative cochain `(0, windingIndex)` in the restriction-cone model.

The cone is indexed so that its degree-one term represents degree-two relative cohomology.
Its second component is the explicit winding-index `1`-cochain on the complement, and its
ambient component is zero. -/
def rawRelativeWindingCochainHom :
    ModuleCat.of ℚ ℚ ⟶
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).X
        (ComplexShape.embeddingUpNat.f 1) :=
  extendedWindingIntegerCochainHom (X := X) g hg ≫
    (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
      (ComplexShape.embeddingUpNat.f 1)

/-- The literal cone cochain is closed. -/
lemma rawRelativeWindingCochainHom_closed :
    rawRelativeWindingCochainHom (X := X) g hg ≫
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) = 0 := by
  dsimp [rawRelativeWindingCochainHom]
  rw [Category.assoc, CochainComplex.mappingCone.inr_f_d]
  rw [← Category.assoc, extendedWindingIntegerCochainHom_closed, zero_comp]

/-- The actual value of the relative cone cocycle (at `1 : ℚ`). -/
def rawRelativeWindingCochain :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).X
      (ComplexShape.embeddingUpNat.f 1) :=
  (rawRelativeWindingCochainHom (X := X) g hg).hom 1

/-- The displayed relative cone cochain is a cocycle. -/
lemma rawRelativeWindingCochain_closed :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
      (rawRelativeWindingCochain (X := X) g hg) = 0 := by
  change ((CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)).hom
        ((rawRelativeWindingCochainHom (X := X) g hg).hom 1) = 0
  simpa using congrArg (fun f => f.hom 1)
    (rawRelativeWindingCochainHom_closed (X := X) g hg)

/-- The ambient component of the cone cochain is zero. -/
lemma rawRelativeWindingCochain_fst :
    ((CochainComplex.mappingCone.fst (relativeCochainRestrictionInt ℚ X)).1.v
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by simp))
      (rawRelativeWindingCochain (X := X) g hg) = 0 := by
  have h : rawRelativeWindingCochainHom (X := X) g hg ≫
      (CochainComplex.mappingCone.fst (relativeCochainRestrictionInt ℚ X)).1.v
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by simp) = 0 := by
    dsimp [rawRelativeWindingCochainHom]
    rw [Category.assoc, CochainComplex.mappingCone.inr_f_fst_v, comp_zero]
  change ((CochainComplex.mappingCone.fst (relativeCochainRestrictionInt ℚ X)).1.v
    (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by simp)).hom
      ((rawRelativeWindingCochainHom (X := X) g hg).hom 1) = 0
  simpa using congrArg (fun f => f.hom 1) h

/-- The complement component of the cone cochain is exactly the extended winding cochain. -/
lemma rawRelativeWindingCochain_snd :
    ((CochainComplex.mappingCone.snd (relativeCochainRestrictionInt ℚ X)).v
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 1) (by simp))
      (rawRelativeWindingCochain (X := X) g hg) =
        extendedWindingIntegerCochainElement (X := X) g hg := by
  have h : rawRelativeWindingCochainHom (X := X) g hg ≫
      (CochainComplex.mappingCone.snd (relativeCochainRestrictionInt ℚ X)).v
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 1) (by simp) =
      extendedWindingIntegerCochainHom (X := X) g hg := by
    dsimp [rawRelativeWindingCochainHom]
    rw [Category.assoc, CochainComplex.mappingCone.inr_f_snd_v, Category.comp_id]
  change ((CochainComplex.mappingCone.snd (relativeCochainRestrictionInt ℚ X)).v
    (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 1) (by simp)).hom
      ((rawRelativeWindingCochainHom (X := X) g hg).hom 1) =
        (extendedWindingIntegerCochainHom (X := X) g hg).hom 1
  simpa using congrArg (fun f => f.hom 1) h

/-- The literal cone cocycle, as a morphism to the cycle object. -/
def rawRelativeWindingCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).cycles
        (ComplexShape.embeddingUpNat.f 1) :=
  (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).liftCycles
    (rawRelativeWindingCochainHom (X := X) g hg)
    (ComplexShape.embeddingUpNat.f 2) (by simp)
    (rawRelativeWindingCochainHom_closed (X := X) g hg)

/-- The literal cone cocycle `(0, windingIndex)` is the image of the literal winding cocycle
under the second inclusion of the restriction cone. -/
lemma extendedWindingIntegerCocycle_cyclesMap_inr :
    extendedWindingIntegerCocycle (X := X) g hg ≫
      HomologicalComplex.cyclesMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X))
        (ComplexShape.embeddingUpNat.f 1) =
    rawRelativeWindingCocycle (X := X) g hg := by
  exact HomologicalComplex.liftCycles_comp_cyclesMap
    (extendedWindingIntegerCochainHom (X := X) g hg)
    (ComplexShape.embeddingUpNat.f 2) (by simp)
    (extendedWindingIntegerCochainHom_closed (X := X) g hg)
    (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X))

/-- Passing to homology preserves the literal cone-inclusion description of the cocycle. -/
lemma extendedWindingIntegerCocycle_homologyMap_inr :
    extendedWindingIntegerCocycle (X := X) g hg ≫
        ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
          ComplexShape.embeddingUpNat).homologyπ (ComplexShape.embeddingUpNat.f 1)) ≫
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X))
          (ComplexShape.embeddingUpNat.f 1) =
      rawRelativeWindingCocycle (X := X) g hg ≫
        (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).homologyπ
          (ComplexShape.embeddingUpNat.f 1) := by
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    extendedWindingIntegerCocycle_cyclesMap_inr]

/-- The degree-two relative singular cohomology class represented by `(0, windingIndex)`. -/
def windingRelativeCochainClass : RelativeCohomology ℚ X 2 :=
  relativeCochainConeCohomologyEquivCanonical ℚ X 2
    ((rawRelativeWindingCocycle (X := X) g hg ≫
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).homologyπ
        (ComplexShape.embeddingUpNat.f 1)).hom 1)

set_option maxHeartbeats 2000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The literal cone cocycle `(0, windingIndex)` evaluates on a relative class by applying
the winding period to its actual connecting boundary.  This identifies the raw mapping-cone
construction with the elementary boundary-period construction, with positive sign. -/
theorem windingRelativeCochainClass_eq_boundaryPeriod :
    windingRelativeCochainClass (X := X) g hg =
      (windingRationalPeriod g hg).comp
        ((relativeChainShortComplex_shortExact ℚ X).δ 2 1
          (ComplexShape.down_mk 2 1 (by simp))).hom := by
  let K := ((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex
  let e := K.extendHomologyIso ComplexShape.embeddingUpNat
    (j := 1) (j' := (1 : ℤ)) rfl
  let a : (relativeDualCochainShortComplexNat ℚ X).X₃.homology 1 :=
    (pairWindingIntegerCocycle (X := X) g hg ≫ K.homologyπ 1).hom 1
  let ae := (extendedWindingIntegerCocycle (X := X) g hg ≫
    (K.extend ComplexShape.embeddingUpNat).homologyπ (1 : ℤ)).hom 1
  have hextclass : e.hom.hom ae = a := by
    change e.hom.hom
      ((extendedWindingIntegerCocycle (X := X) g hg ≫
        (K.extend ComplexShape.embeddingUpNat).homologyπ (1 : ℤ)).hom 1) =
      (pairWindingIntegerCocycle (X := X) g hg ≫ K.homologyπ 1).hom 1
    have hπ := ConcreteCategory.congr_hom
      (K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat
        (j := 1) (j' := (1 : ℤ)) rfl)
      ((extendedWindingIntegerCocycle (X := X) g hg).hom 1)
    change e.hom.hom
      ((K.extend ComplexShape.embeddingUpNat).homologyπ (1 : ℤ) |>.hom
          ((extendedWindingIntegerCocycle (X := X) g hg).hom 1)) =
        (K.homologyπ 1).hom
          ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := 1) rfl).hom.hom
            ((extendedWindingIntegerCocycle (X := X) g hg).hom 1)) at hπ
    change e.hom.hom
      ((K.extend ComplexShape.embeddingUpNat).homologyπ (1 : ℤ) |>.hom
        ((extendedWindingIntegerCocycle (X := X) g hg).hom 1)) = _
    rw [hπ]
    have ht := ConcreteCategory.congr_hom
      (extendedWindingIntegerCocycle_transport (X := X) g hg) 1
    change (K.homologyπ 1).hom
      ((K.extendCyclesIso ComplexShape.embeddingUpNat (j := 1) rfl).hom.hom
        ((extendedWindingIntegerCocycle (X := X) g hg).hom 1)) =
      (K.homologyπ 1).hom ((pairWindingIntegerCocycle (X := X) g hg).hom 1)
    apply congrArg (K.homologyπ 1).hom
    simpa only [ConcreteCategory.comp_apply] using ht
  have hpre : e.inv.hom a = ae := by
    apply e.toLinearEquiv.injective
    change e.hom.hom (e.inv.hom a) = e.hom.hom ae
    calc
      e.hom.hom (e.inv.hom a) = a := e.toLinearEquiv.apply_symm_apply a
      _ = e.hom.hom ae := hextclass.symm
  have hcone :
      relativeCochainConeCohomologyEquivCanonical ℚ X 2
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.triangle
            (relativeCochainRestrictionInt ℚ X)).mor₂ 1).hom (e.inv.hom a)) =
        windingRelativeCochainClass (X := X) g hg := by
    rw [hpre]
    apply congrArg (relativeCochainConeCohomologyEquivCanonical ℚ X 2)
    change (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X))
      (ComplexShape.embeddingUpNat.f 1)).hom
      ((extendedWindingIntegerCocycle (X := X) g hg ≫
        ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
          ComplexShape.embeddingUpNat).homologyπ
            (ComplexShape.embeddingUpNat.f 1))).hom 1) =
      (rawRelativeWindingCocycle (X := X) g hg ≫
        (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)).hom 1
    simpa only [ConcreteCategory.comp_apply] using congrArg (fun f => f.hom 1)
      (extendedWindingIntegerCocycle_homologyMap_inr (X := X) g hg)
  calc
    windingRelativeCochainClass (X := X) g hg =
        relativeCochainConeCohomologyEquivCanonical ℚ X 2
          ((HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.triangle
              (relativeCochainRestrictionInt ℚ X)).mor₂ 1).hom (e.inv.hom a)) := hcone.symm
    _ = (HomologicalComplex.linearDualHomologyEquiv
          ((chainPairFunctor ℚ).obj X).left 1 a).comp
          ((relativeChainShortComplex_shortExact ℚ X).δ 2 1
            (ComplexShape.down_mk 2 1 (by simp))).hom :=
      relativeCochainCone_rawBoundary ℚ X a
    _ = (windingRationalPeriod g hg).comp
          ((relativeChainShortComplex_shortExact ℚ X).δ 2 1
            (ComplexShape.down_mk 2 1 (by simp))).hom := by
      rw [show HomologicalComplex.linearDualHomologyEquiv
        ((chainPairFunctor ℚ).obj X).left 1 a = windingRationalPeriod g hg by
          exact pairWindingIntegerCocycle_class_eq_windingRationalPeriod (X := X) g hg]

/-- The relative class represented by `(0, windingIndex)` is the singular-cohomology image of
the explicitly displayed winding cocycle under the second cone inclusion. -/
theorem windingRelativeCochainClass_eq_coneInclusion :
    windingRelativeCochainClass (X := X) g hg =
      relativeCochainConeCohomologyEquivCanonical ℚ X 2
        ((HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X))
          (ComplexShape.embeddingUpNat.f 1)).hom
          ((extendedWindingIntegerCocycle (X := X) g hg ≫
            (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
              ComplexShape.embeddingUpNat).homologyπ
                (ComplexShape.embeddingUpNat.f 1)).hom 1)) := by
  apply congrArg (relativeCochainConeCohomologyEquivCanonical ℚ X 2)
  change (rawRelativeWindingCocycle (X := X) g hg ≫
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).homologyπ
        (ComplexShape.embeddingUpNat.f 1)).hom 1 =
    ((extendedWindingIntegerCocycle (X := X) g hg ≫
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).homologyπ (ComplexShape.embeddingUpNat.f 1)) ≫
      HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X))
        (ComplexShape.embeddingUpNat.f 1)).hom 1
  simpa only [ConcreteCategory.comp_apply] using congrArg (fun f => f.hom 1)
    (extendedWindingIntegerCocycle_homologyMap_inr (X := X) g hg).symm

variable {P Q : TopPair.{0}} (f : P ⟶ Q) (g : C(Q.snd, ℂ)) (hg : ∀ y, g y ≠ 0)

/-- Pull the literal winding cone cochain back along a map of pairs.  In particular, this is how
the standard normal cochain is placed in a flattened chart around a divisor. -/
def rawRelativeWindingCochainPullback :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).X
      (ComplexShape.embeddingUpNat.f 1) :=
  (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1)
    (rawRelativeWindingCochain (X := Q) g hg)

/-- The pulled-back literal cochain, as a morphism from the scalar object. -/
def rawRelativeWindingCochainPullbackHom :
    ModuleCat.of ℚ ℚ ⟶
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).X
        (ComplexShape.embeddingUpNat.f 1) :=
  rawRelativeWindingCochainHom (X := Q) g hg ≫
    (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1)

/-- Pullback preserves the explicit cocycle equation. -/
lemma rawRelativeWindingCochainPullback_closed :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).d
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
      (rawRelativeWindingCochainPullback f g hg) = 0 := by
  change ((relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1) ≫
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)).hom
        (rawRelativeWindingCochain (X := Q) g hg) = 0
  rw [(relativeCochainConeMap ℚ f).comm]
  change (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 2)
    ((CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ Q)).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
        (rawRelativeWindingCochain (X := Q) g hg)) = 0
  rw [rawRelativeWindingCochain_closed]
  exact map_zero _

lemma rawRelativeWindingCochainPullbackHom_closed :
    rawRelativeWindingCochainPullbackHom f g hg ≫
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).d
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) = 0 := by
  dsimp [rawRelativeWindingCochainPullbackHom]
  rw [Category.assoc, (relativeCochainConeMap ℚ f).comm]
  rw [← Category.assoc, rawRelativeWindingCochainHom_closed, zero_comp]

/-- The pulled-back literal cochain, regarded as a cycle. -/
def rawRelativeWindingCocyclePullback :
    ModuleCat.of ℚ ℚ ⟶
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).cycles
        (ComplexShape.embeddingUpNat.f 1) :=
  (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).liftCycles
    (rawRelativeWindingCochainPullbackHom f g hg)
    (ComplexShape.embeddingUpNat.f 2) (by simp)
    (rawRelativeWindingCochainPullbackHom_closed f g hg)

/-- Pulling back the displayed cocycle is the cycles-map image of the original displayed
cocycle. -/
lemma rawRelativeWindingCocyclePullback_eq_cyclesMap :
    rawRelativeWindingCocyclePullback f g hg =
      rawRelativeWindingCocycle (X := Q) g hg ≫
        HomologicalComplex.cyclesMap (relativeCochainConeMap ℚ f)
          (ComplexShape.embeddingUpNat.f 1) := by
  exact (HomologicalComplex.liftCycles_comp_cyclesMap
    (rawRelativeWindingCochainHom (X := Q) g hg)
    (ComplexShape.embeddingUpNat.f 2) (by simp)
    (rawRelativeWindingCochainHom_closed (X := Q) g hg)
    (relativeCochainConeMap ℚ f)).symm

end ChernWinding
