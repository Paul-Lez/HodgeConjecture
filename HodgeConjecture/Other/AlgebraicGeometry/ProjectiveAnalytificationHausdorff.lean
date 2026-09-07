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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineScheme
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexOpen
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytification
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Hausdorff analytifications of projective complex schemes

The analytification of an affine complex scheme is Hausdorff because global regular functions
separate its complex points. Any two points of finite-dimensional projective space lie in a
common affine basic open: an explicit integral linear form can be chosen not to vanish at either
of two homogeneous coordinate vectors. Pulling this open back along a closed projective
presentation proves that every projective complex scheme has Hausdorff analytification.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry

namespace ComplexPoint

/-- The analytification of an affine complex scheme is Hausdorff. -/
lemma t2Space_of_isAffine {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) [IsAffine X] :
    @T2Space (ComplexPoint X structureMap) analyticTopology := by
  let _ : TopologicalSpace (ComplexPoint X structureMap) := analyticTopology
  rw [t2Space_iff_nhds]
  intro z w hzw
  have happ : z.1.appTop ≠ w.1.appTop := by
    intro h
    apply hzw
    apply Subtype.ext
    exact ext_of_isAffine h
  have hex : ∃ s : Γ(X, ⊤),
      (Scheme.ΓSpecIso (.of ℂ)).hom (z.1.appTop s) ≠
        (Scheme.ΓSpecIso (.of ℂ)).hom (w.1.appTop s) := by
    by_contra hn
    push Not at hn
    apply happ
    ext s
    exact (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.injective (hn s)
  obtain ⟨s, hs⟩ := hex
  have heval : evaluate ⊤ s z ≠ evaluate ⊤ s w := by
    simpa only [evaluate_top_eq_appTop] using hs
  obtain ⟨U, V, hU, hV, hzU, hwV, hUV⟩ := t2_separation heval
  refine ⟨evaluate ⊤ s ⁻¹' U,
    (hU.preimage (continuous_evaluate_top s)).mem_nhds hzU,
    evaluate ⊤ s ⁻¹' V,
    (hV.preimage (continuous_evaluate_top s)).mem_nhds hwV, ?_⟩
  exact hUV.preimage _

/-- A complex scheme whose every pair of complex points lies in a common affine open has a
Hausdorff analytification. -/
lemma t2Space_of_pair_mem_affineOpen {X : Scheme}
    (structureMap : X ⟶ Spec (.of ℂ))
    (hpair : ∀ z w : ComplexPoint X structureMap,
      ∃ U : X.Opens, z ∈ overOpen U ∧ w ∈ overOpen U ∧ IsAffine U.toScheme) :
    @T2Space (ComplexPoint X structureMap) analyticTopology := by
  let _ : TopologicalSpace (ComplexPoint X structureMap) := analyticTopology
  rw [t2Space_iff_nhds]
  intro z w hzw
  obtain ⟨U, hzU, hwU, hUaff⟩ := hpair z w
  let structureMapU : U.toScheme ⟶ Spec (.of ℂ) := U.ι ≫ structureMap
  let _ : IsAffine U.toScheme := hUaff
  let _ : TopologicalSpace (ComplexPoint U.toScheme structureMapU) := analyticTopology
  let _ : T2Space (ComplexPoint U.toScheme structureMapU) :=
    t2Space_of_isAffine structureMapU
  let _ : TopologicalSpace {q : ComplexPoint X structureMap // q ∈ overOpen U} :=
    TopologicalSpace.induced Subtype.val analyticTopology
  let _ : T2Space {q : ComplexPoint X structureMap // q ∈ overOpen U} :=
    (openHomeomorph U structureMap).t2Space
  let zU : {q : ComplexPoint X structureMap // q ∈ overOpen U} := ⟨z, hzU⟩
  let wU : {q : ComplexPoint X structureMap // q ∈ overOpen U} := ⟨w, hwU⟩
  have hzwU : zU ≠ wU := by
    intro h
    exact hzw (congrArg Subtype.val h)
  obtain ⟨A, B, hA, hB, hzA, hwB, hAB⟩ := t2_separation hzwU
  let e : {q : ComplexPoint X structureMap // q ∈ overOpen U} →
      ComplexPoint X structureMap := Subtype.val
  have he : IsOpenEmbedding e := (isOpen_overOpen U).isOpenEmbedding_subtypeVal
  refine ⟨e '' A, (he.isOpenMap A hA).mem_nhds ⟨zU, hzA, rfl⟩,
    e '' B, (he.isOpenMap B hB).mem_nhds ⟨wU, hwB, rfl⟩, ?_⟩
  exact Set.disjoint_image_of_injective he.injective hAB

end ComplexPoint

namespace ComplexProjectiveSpace

open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- There is an integral linear form which is nonzero on each of two nonzero complex coordinate
vectors. -/
lemma exists_common_nonvanishing_linearForm {n : ℕ}
    (v w : CoordinateSpace n) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ r : UniversalRing n,
      r ∈ UniversalGrading n 1 ∧
      (Scheme.ΓSpecIso (.of ℂ)).hom (coordinateGlobalSectionsHom v r) ≠ 0 ∧
      (Scheme.ΓSpecIso (.of ℂ)).hom (coordinateGlobalSectionsHom w r) ≠ 0 := by
  let i := coordinateIndex v hv
  have hvi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  by_cases hwi : w i ≠ 0
  · refine ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X _ _, ?_, ?_⟩
    · simpa using hvi
    · simpa using hwi
  · let j := coordinateIndex w hw
    have hwj : w j ≠ 0 := coordinateIndex_ne_zero w hw
    have hwi0 : w i = 0 := not_ne_iff.mp hwi
    by_cases hvij : v i + v j ≠ 0
    · refine ⟨MvPolynomial.X i + MvPolynomial.X j,
        (UniversalGrading n 1).add_mem
          (MvPolynomial.isHomogeneous_X _ _)
          (MvPolynomial.isHomogeneous_X _ _), ?_, ?_⟩
      · simpa using hvij
      · simpa [coordinateGlobalSectionsHom_X, hwi0] using hwj
    · refine ⟨MvPolynomial.X i - MvPolynomial.X j,
        (UniversalGrading n 1).sub_mem
          (MvPolynomial.isHomogeneous_X _ _)
          (MvPolynomial.isHomogeneous_X _ _), ?_, ?_⟩
      · push Not at hvij
        have hvj : v j = -v i := by linear_combination hvij
        simp only [map_sub, coordinateGlobalSectionsHom_X]
        simp
        rw [hvj]
        simpa using hvi
      · simpa [coordinateGlobalSectionsHom_X, hwi0] using hwj

/-- A homogeneous polynomial is nonzero at a coordinate vector exactly when the corresponding
projective point lies in its basic open. -/
lemma chartIntegralProjAt_preimage_basicOpen {n d : ℕ}
    (v : CoordinateSpace n) (i : Fin (n + 1)) (hi : v i ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    chartIntegralProjAt v i hi ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r =
      if coordinateEvaluationHom v r = 0 then ⊥ else ⊤ := by
  unfold chartIntegralProjAt
  rw [Scheme.Hom.comp_preimage]
  rw [show Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) r =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i) hr) by
    exact Proj.awayι_preimage_basicOpen
      (𝒜 := UniversalGrading n) (f := MvPolynomial.X i) (g := r)
      (m := 1) (m' := d)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one hr hd]
  rw [SpecMap_preimage_basicOpen]
  rw [show HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) hr =
      HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) i) d r (by simpa using hr) by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem]]
  simp only [CommRingCat.hom_ofHom]
  rw [awayCoordinateEvaluation_mk v i hi d r hr]
  split_ifs with h
  · rw [h, zero_mul, PrimeSpectrum.basicOpen_zero]
    rfl
  · apply top_unique
    intro x hx
    change coordinateEvaluationHom v r * (v i)⁻¹ ^ d ∉ x.asIdeal
    rw [Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using mul_ne_zero h (pow_ne_zero d (inv_ne_zero hi))

/-- The basic-open membership formula without fixing the selected standard coordinate chart. -/
lemma chartIntegralProj_preimage_basicOpen {n d : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r =
      if coordinateEvaluationHom v r = 0 then ⊥ else ⊤ := by
  let i := coordinateIndex v hv
  let hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi]
  exact chartIntegralProjAt_preimage_basicOpen v i hi r hd hr

/-- The inverse image of a projective-spectrum basic open in complex projective space. -/
noncomputable def projectiveSpaceBasicOpen (n : ℕ) (r : UniversalRing n) :
    (ProjectiveSpace (Fin (n + 1)) (Spec (.of ℂ))).Opens :=
  Limits.pullback.snd
      (Limits.terminal.from (Spec (.of ℂ)))
      (Limits.terminal.from (Proj (UniversalGrading n))) ⁻¹ᵁ
    Proj.basicOpen (UniversalGrading n) r

set_option linter.style.haveILetI false in
/-- A positive-degree basic open in complex projective space is affine. -/
lemma projectiveSpaceBasicOpen_isAffine {n d : ℕ}
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    IsAffine (projectiveSpaceBasicOpen n r).toScheme := by
  haveI : IsAffineHom (Limits.terminal.from (Spec (.of ℂ))) := inferInstance
  haveI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom)
      (Limits.terminal.from (Proj (UniversalGrading n))) :=
    { of_isPullback := fun pb h ↦
        MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h }
  have hsnd : IsAffineHom (Limits.pullback.snd
      (Limits.terminal.from (Spec (.of ℂ)))
      (Limits.terminal.from (Proj (UniversalGrading n)))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact @IsAffineHom.isAffine_preimage _ _ _ hsnd
    (Proj.basicOpen (UniversalGrading n) r)
    (Proj.isAffineOpen_basicOpen
      (𝒜 := UniversalGrading n) (f := r) hr hd)

/-- A coordinate point lies in the projective-space basic open whenever the defining homogeneous
polynomial is nonzero on its coordinates. -/
lemma vectorToComplexPoint_mem_projectiveSpaceBasicOpen {n d : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d)
    (hne : coordinateEvaluationHom v r ≠ 0) :
    vectorToComplexPoint v hv ∈ ComplexPoint.overOpen (projectiveSpaceBasicOpen n r) := by
  change (vectorToProjectiveSpace v hv) (IsLocalRing.closedPoint ℂ) ∈
    projectiveSpaceBasicOpen n r
  unfold projectiveSpaceBasicOpen
  change ((vectorToProjectiveSpace v hv) ≫ Limits.pullback.snd
    (Limits.terminal.from (Spec (.of ℂ)))
    (Limits.terminal.from (Proj (UniversalGrading n))))
      (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen (UniversalGrading n) r
  rw [vectorToProjectiveSpace_toProj]
  change IsLocalRing.closedPoint ℂ ∈
    chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r
  rw [chartIntegralProj_preimage_basicOpen v hv r hd hr, if_neg hne]
  trivial

/-- Any two complex points of finite-dimensional projective space lie in a common affine open. -/
lemma projectiveSpace_pair_mem_affineOpen (n : ℕ)
    (z w : ComplexPoint (ProjectiveSpace (Fin (n + 1)) (Spec (.of ℂ)))
      (ProjectiveSpace.toBase (Fin (n + 1)) (Spec (.of ℂ)))) :
    ∃ U : (ProjectiveSpace (Fin (n + 1)) (Spec (.of ℂ))).Opens,
      z ∈ ComplexPoint.overOpen U ∧ w ∈ ComplexPoint.overOpen U ∧ IsAffine U.toScheme := by
  obtain ⟨v, hvz⟩ := surjective_vectorToComplexPoint z
  obtain ⟨u, huw⟩ := surjective_vectorToComplexPoint w
  obtain ⟨r, hr, hrv, hru⟩ :=
    exists_common_nonvanishing_linearForm v.1 u.1 v.2 u.2
  refine ⟨projectiveSpaceBasicOpen n r, ?_, ?_,
    projectiveSpaceBasicOpen_isAffine r zero_lt_one hr⟩
  · rw [← hvz]
    exact vectorToComplexPoint_mem_projectiveSpaceBasicOpen
      v.1 v.2 r zero_lt_one hr hrv
  · rw [← huw]
    exact vectorToComplexPoint_mem_projectiveSpaceBasicOpen
      u.1 u.2 r zero_lt_one hr hru

/-- Finite-dimensional scheme-theoretic complex projective space is Hausdorff. -/
noncomputable instance instT2SpaceProjectiveSpaceComplexPoint (n : ℕ) :
    T2Space
      (ComplexPoint (ProjectiveSpace (Fin (n + 1)) (Spec (.of ℂ)))
        (ProjectiveSpace.toBase (Fin (n + 1)) (Spec (.of ℂ)))) :=
  ComplexPoint.t2Space_of_pair_mem_affineOpen
    (ProjectiveSpace.toBase (Fin (n + 1)) (Spec (.of ℂ)))
    (projectiveSpace_pair_mem_affineOpen n)

end ComplexProjectiveSpace

namespace ProjectiveSpace.Presentation

set_option linter.style.haveILetI false in
/-- Any two complex points of a projective presentation lie in a common affine open. -/
lemma pair_mem_affineOpen {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (P : ProjectiveSpace.Presentation f) (z w : ComplexPoint X f) :
    ∃ U : X.Opens, z ∈ ComplexPoint.overOpen U ∧
      w ∈ ComplexPoint.overOpen U ∧ IsAffine U.toScheme := by
  obtain ⟨U, hzU, hwU, hUaff⟩ :=
    ComplexProjectiveSpace.projectiveSpace_pair_mem_affineOpen P.ambientDimension
      (analyticImmersion P z) (analyticImmersion P w)
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  refine ⟨P.immersion ⁻¹ᵁ U,
    (ComplexPoint.mem_overOpen_map_iff P.immersion P.immersion_toBase z U).mp hzU,
    (ComplexPoint.mem_overOpen_map_iff P.immersion P.immersion_toBase w U).mp hwU, ?_⟩
  exact @IsAffineHom.isAffine_preimage _ _ P.immersion inferInstance U hUaff

/-- The analytification of an explicit projective presentation is Hausdorff. -/
theorem complexPoint_t2Space {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (P : ProjectiveSpace.Presentation f) :
    @T2Space (ComplexPoint X f) ComplexPoint.analyticTopology :=
  ComplexPoint.t2Space_of_pair_mem_affineOpen f (pair_mem_affineOpen P)

end ProjectiveSpace.Presentation

namespace ProjectiveSpace.IsProjective

/-- The analytification of a projective complex scheme is Hausdorff. -/
noncomputable instance complexPoint_t2Space {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    [h : ProjectiveSpace.IsProjective f] : T2Space (ComplexPoint X f) :=
  ProjectiveSpace.Presentation.complexPoint_t2Space
    (Classical.choice h.nonempty_presentation)

end ProjectiveSpace.IsProjective

end AlgebraicGeometry
