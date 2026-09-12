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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexEtale

import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Étale algebras are local homeomorphisms on complex points

Restricting a complex point of an étale algebra to its polynomial base is a local
homeomorphism. The standard étale case is the implicit function theorem applied to the defining
equation, packaged in `ComplexEtale.lean` as a projection chart; the general case localizes at
the kernel of each complex point and appeals to Mathlib's standard étale local presentation
theorem.

The analytic charts the conjecture is stated with come from `localEtaleCoordinates`, which uses
the projection charts directly, so this packaging is not needed to state the conjecture.
-/

@[expose] public section

open CategoryTheory Topology Filter
open scoped Polynomial Topology ContDiff

namespace AlgebraicGeometry.ComplexAlgHom

open ComplexPoint Point

noncomputable section

variable {n : ℕ} (P : StandardEtalePair (complexPolynomialRing n))

/-- Restriction of a complex point of a standard étale algebra to the polynomial base. -/
def standardEtaleBaseAlgHom (u : P.Ring →ₐ[ℂ] ℂ) : complexPolynomialRing n →ₐ[ℂ] ℂ :=
  u.comp (IsScalarTower.toAlgHom ℂ (complexPolynomialRing n) P.Ring)

/-- On complex algebra homomorphisms, a standard étale algebra is locally homeomorphic to its
polynomial base by restriction. -/
lemma isLocalHomeomorph_standardEtaleBaseAlgHom :
    IsLocalHomeomorph (standardEtaleBaseAlgHom P) := by
  have hcoordinates := (isLocalHomeomorph_standardEtaleCoordinateProjection P).comp
    (standardEtaleCoordinateHomeomorph P).isLocalHomeomorph
  have h := (mvPolynomialAlgHomHomeomorph n).symm.isLocalHomeomorph.comp hcoordinates
  convert h using 1
  exact funext fun _ ↦ ((mvPolynomialAlgHomHomeomorph n).symm_apply_apply _).symm

variable (S : Type) [CommRing S] [Algebra ℂ S]
  [Algebra (complexPolynomialRing n) S]
  [IsScalarTower ℂ (complexPolynomialRing n) S]
  [Algebra.IsStandardEtale (complexPolynomialRing n) S]

/-- Restriction to the polynomial base is a local homeomorphism for every standard étale
algebra. -/
lemma isLocalHomeomorph_isStandardEtaleBaseAlgHom :
    IsLocalHomeomorph (isStandardEtaleBaseAlgHom (n := n) S) := by
  let e := standardEtalePresentationComplexAlgEquiv (n := n) S
  let Q := (chosenStandardEtalePresentation (n := n) S).P
  have h := (isLocalHomeomorph_standardEtaleBaseAlgHom Q).comp
    (precompAlgEquivHomeomorph e).symm.isLocalHomeomorph
  convert h using 1
  funext u
  apply AlgHom.ext
  intro b
  change u (algebraMap (complexPolynomialRing n) S b) =
    u (e.symm (algebraMap (complexPolynomialRing n) Q.Ring b))
  congr 1
  have hb := (chosenStandardEtalePresentation (n := n) S).equivRing.commutes b
  change e (algebraMap (complexPolynomialRing n) S b) =
    algebraMap (complexPolynomialRing n) Q.Ring b at hb
  rw [← hb, e.symm_apply_apply]

variable {S}

variable (T : Type) [CommRing T] [Algebra ℂ T]
  [Algebra (complexPolynomialRing n) T]
  [IsScalarTower ℂ (complexPolynomialRing n) T]
  [Algebra.Etale (complexPolynomialRing n) T]

/-- Restriction to the polynomial base is a local homeomorphism for every étale algebra. The
proof localizes at the kernel of each complex point and uses Mathlib's standard étale local
presentation theorem. -/
lemma isLocalHomeomorph_etaleBaseAlgHom :
    IsLocalHomeomorph (etaleBaseAlgHom (n := n) T) := by
  intro u
  let Q : Ideal T := RingHom.ker u.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime u.toRingHom
  let : Algebra.IsEtaleAt (complexPolynomialRing n) Q := by
    have : Algebra.FormallyEtale T (Localization.AtPrime Q) :=
      Algebra.FormallyEtale.of_isLocalization Q.primeCompl
    exact Algebra.FormallyEtale.comp (complexPolynomialRing n) T (Localization.AtPrime Q)
  obtain ⟨f, hfQ, hfstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := complexPolynomialRing n) Q
  let : Algebra.IsStandardEtale (complexPolynomialRing n) (Localization.Away f) := hfstd
  have hfu : u f ≠ 0 := by
    simpa [Q, RingHom.mem_ker] using hfQ
  let j := localizationAwayAlgHomMap T f
  let F := etaleBaseAlgHom (n := n) T
  let G := isStandardEtaleBaseAlgHom (n := n) (Localization.Away f)
  have hj : IsLocalHomeomorph j := isLocalHomeomorph_localizationAwayAlgHomMap T f
  have hG : IsLocalHomeomorph G :=
    isLocalHomeomorph_isStandardEtaleBaseAlgHom (n := n) (Localization.Away f)
  have hcomp : G = F ∘ j := funext fun _ ↦ AlgHom.ext fun _ ↦ rfl
  have hFG : IsLocalHomeomorph (F ∘ j) := hcomp ▸ hG
  have hFonImage : IsLocalHomeomorphOn F (j '' Set.univ) :=
    hFG.isLocalHomeomorphOn.of_comp_right (s := Set.univ) hj.isLocalHomeomorphOn
  have hFon : IsLocalHomeomorphOn F (Set.range j) := by
    simpa only [Set.image_univ] using hFonImage
  have hu : u ∈ Set.range j := by
    let v := (localizationAwayAlgHomHomeomorph T f).symm ⟨u, hfu⟩
    refine ⟨v, ?_⟩
    change ((localizationAwayAlgHomHomeomorph T f) v).1 = u
    rw [Homeomorph.apply_symm_apply]
  exact hFon u hu

end

end AlgebraicGeometry.ComplexAlgHom

namespace AlgebraicGeometry.ComplexPoint

open ComplexAlgHom Point

noncomputable section

variable {n : ℕ} (P : StandardEtalePair (complexPolynomialRing n))

/-- The map on complex points associated to a standard étale algebra. -/
def standardEtaleComplexPointMap :
    ComplexPoint (Over.mk (affineSpecStructureMap P.Ring)) →
      ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n))) :=
  Point.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (complexPolynomialRing n) P.Ring)))
    (specMap_algebraMap_comp_affineSpecStructureMap P))

lemma affineSpecEquiv_standardEtaleComplexPointMap
    (z : ComplexPoint (Over.mk (affineSpecStructureMap P.Ring))) :
    affineSpecEquiv (complexPolynomialRing n) (standardEtaleComplexPointMap P z) =
      standardEtaleBaseAlgHom P (affineSpecEquiv P.Ring z) := by
  ext b
  simp [standardEtaleComplexPointMap, Point.map, affineSpecEquiv,
    standardEtaleBaseAlgHom, Spec.preimage_comp]

/-- A standard étale morphism of affine complex schemes is a local homeomorphism on complex
points. -/
lemma isLocalHomeomorph_standardEtaleComplexPointMap :
    @IsLocalHomeomorph
      (ComplexPoint (Over.mk (affineSpecStructureMap P.Ring)))
      (ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n))))
      analyticTopology analyticTopology (standardEtaleComplexPointMap P) := by
  let : TopologicalSpace
      (ComplexPoint (Over.mk (affineSpecStructureMap P.Ring))) := analyticTopology
  let : TopologicalSpace
      (ComplexPoint (Over.mk (affineSpecStructureMap (complexPolynomialRing n)))) := analyticTopology
  have h := (affineSpecHomeomorph (complexPolynomialRing n)).symm.isLocalHomeomorph.comp
    ((isLocalHomeomorph_standardEtaleBaseAlgHom P).comp
      (affineSpecHomeomorph P.Ring).isLocalHomeomorph)
  convert h using 1
  exact funext fun z ↦
    (Homeomorph.eq_symm_apply _).mpr (affineSpecEquiv_standardEtaleComplexPointMap P z)

end

end AlgebraicGeometry.ComplexPoint
