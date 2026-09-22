/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache License, Version 2.0 (the "License");
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

public import Other.AlgebraicTopology.WindingCochainTransition

/-!
# The explicit relative boundary of a unit

A transition function on the overlap of two divisor charts is nonzero on the *whole* overlap
chart, not merely on the complement of the divisor.  Consequently its relative winding cochain
is a boundary.  This file records the intended literal primitive: the ambient winding cochain,
inserted into the first summand of the relative mapping cone.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology.Singular

namespace ChernWinding

variable {X : TopPair.{0}} (g : C(X.fst, ℂ)) (hg : ∀ x, g x ≠ 0)

/-!
The next lemma is intentionally kept at the raw-cochain level.  It says that pulling the
displayed relative winding cochain through an honest map of pairs is the displayed winding
cochain of the pulled-back function.  This is the bridge needed when the two affine charts of
the projective-plane example are restricted to their overlap.
-/

variable {P Q : TopPair.{0}}

/-- Pullback of the literal relative winding cochain is literally the winding cochain of the
pulled-back function. -/
theorem rawRelativeWindingCochainPullback_eq_rawRelativeWindingCochain
    (f : P ⟶ Q) (g : C(Q.snd, ℂ)) (hg : ∀ y, g y ≠ 0) :
    rawRelativeWindingCochainPullback f g hg =
      rawRelativeWindingCochain (X := P) (g.comp (topMap (TopPair.Hom.snd f)))
        (fun x => hg (TopPair.Hom.snd f x)) := by
  rw [rawRelativeWindingCochainPullback,
    rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement,
    rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement]
  have hinr :
      CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ Q) ≫
          relativeCochainConeMap ℚ f =
        (relativeDualCochainShortComplexIntMap ℚ f).τ₃ ≫
          CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ P) := by
    simp [relativeCochainConeMap, CochainComplex.mappingCone.map]
    rfl
  have hτ₃ :
      (relativeDualCochainShortComplexIntMap ℚ f).τ₃.f
        (ComplexShape.embeddingUpNat.f 1)
        (extendedWindingIntegerCochainElement (X := Q) g hg) =
      extendedWindingIntegerCochainElement (X := P)
        (g.comp (topMap (TopPair.Hom.snd f)))
          (fun x => hg (TopPair.Hom.snd f x)) := by
    let KQ := ((chainPairFunctor ℚ).obj Q).left.linearDualCochainComplex
    let KP := ((chainPairFunctor ℚ).obj P).left.linearDualCochainComplex
    let eQ := KQ.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
    let eP := KP.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
    apply (ModuleCat.mono_iff_injective eP.hom).mp inferInstance
    rw [show (relativeDualCochainShortComplexIntMap ℚ f).τ₃.f
        (ComplexShape.embeddingUpNat.f 1) =
          eQ.hom ≫
            (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).map f).left).f 1 ≫
              eP.inv by
      exact HomologicalComplex.extendMap_f
        (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).map f).left)
        ComplexShape.embeddingUpNat rfl]
    change eP.hom (eP.inv
        ((HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).map f).left).f 1
          (eQ.hom (extendedWindingIntegerCochainElement (X := Q) g hg)))) =
      eP.hom (extendedWindingIntegerCochainElement (X := P)
        (g.comp (topMap (TopPair.Hom.snd f))) (fun x => hg (TopPair.Hom.snd f x)))
    rw [eP.inv_hom_id_apply]
    rw [extendedWindingIntegerCochainElement_transport]
    rw [extendedWindingIntegerCochainElement_transport (X := P)
      (g.comp (topMap (TopPair.Hom.snd f))) (fun x => hg (TopPair.Hom.snd f x))]
    change (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).map f).left).f 1
        (pairWindingIntegerCochainElement (X := Q) g hg) =
      pairWindingIntegerCochainElement (X := P)
        (g.comp (topMap (TopPair.Hom.snd f))) (fun x => hg (TopPair.Hom.snd f x))
    rw [HomologicalComplex.linearDualMap_f]
    apply LinearMap.ext
    intro z
    change (windingIntegerCochain g hg).hom
        ((((chainPairFunctor ℚ).map f).left.f 1).hom z) =
      (windingIntegerCochain (g.comp (topMap (TopPair.Hom.snd f)))
        (fun x => hg (TopPair.Hom.snd f x))).hom z
    have hnat := chainComplexMap_comp_windingIntegerCochain
      g hg (TopPair.Hom.snd f) (fun x => hg (TopPair.Hom.snd f x))
    change ((chainPairFunctor ℚ).map f).left.f 1 ≫ windingIntegerCochain g hg =
      windingIntegerCochain (g.comp (topMap (TopPair.Hom.snd f)))
        (fun x => hg (TopPair.Hom.snd f x)) at hnat
    exact ConcreteCategory.congr_hom hnat z
  have hinr_eval := ConcreteCategory.congr_hom
    (congrArg (fun F => F.f (ComplexShape.embeddingUpNat.f 1)) hinr)
    (extendedWindingIntegerCochainElement (X := Q) g hg)
  have hinr_eval' :
      (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1)
          ((CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ Q)).f
            (ComplexShape.embeddingUpNat.f 1)
              (extendedWindingIntegerCochainElement (X := Q) g hg)) =
        (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ P)).f
          (ComplexShape.embeddingUpNat.f 1)
            ((relativeDualCochainShortComplexIntMap ℚ f).τ₃.f
              (ComplexShape.embeddingUpNat.f 1)
              (extendedWindingIntegerCochainElement (X := Q) g hg)) := by
    change (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1)
        ((CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ Q)).f
          (ComplexShape.embeddingUpNat.f 1)
            (extendedWindingIntegerCochainElement (X := Q) g hg)) =
      (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ P)).f
        (ComplexShape.embeddingUpNat.f 1)
          ((relativeDualCochainShortComplexIntMap ℚ f).τ₃.f
            (ComplexShape.embeddingUpNat.f 1)
              (extendedWindingIntegerCochainElement (X := Q) g hg)) at hinr_eval
    exact hinr_eval
  change (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1)
      ((CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ Q)).f
        (ComplexShape.embeddingUpNat.f 1)
          (extendedWindingIntegerCochainElement (X := Q) g hg)) = _
  rw [hinr_eval', hτ₃]

/-- The literal ambient winding cochain after the same integer-indexed extension used in the
relative cone.  This is a direct formula, not an extension chosen by surjectivity. -/
def ambientExtendedWindingIntegerCochainElement :
    (((SingularChainComplex ℚ X.fst).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).X (ComplexShape.embeddingUpNat.f 1)) :=
  (((SingularChainComplex ℚ X.fst).linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat (i := 1) rfl).inv)
      ((windingIntegerCochain g hg).hom)

/-- The displayed ambient winding cochain is closed. -/
lemma ambientExtendedWindingIntegerCochainElement_closed :
    ((SingularChainComplex ℚ X.fst).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).d 1 2
      (ambientExtendedWindingIntegerCochainElement (X := X) g hg) = 0 := by
  let K := (singularChains X.fst).linearDualCochainComplex
  let e₁ := K.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
  let e₂ := K.extendXIso ComplexShape.embeddingUpNat (i := 2) rfl
  change ((K.extend ComplexShape.embeddingUpNat).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)).hom
    (e₁.inv.hom ((windingIntegerCochain g hg).hom)) = 0
  rw [show (K.extend ComplexShape.embeddingUpNat).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) =
      e₁.hom ≫ K.d 1 2 ≫ e₂.inv by
    exact HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat rfl rfl]
  simp only [ConcreteCategory.comp_apply]
  have hcancel : e₁.hom (e₁.inv ((windingIntegerCochain g hg).hom)) =
      (windingIntegerCochain g hg).hom :=
    ConcreteCategory.congr_hom e₁.inv_hom_id (windingIntegerCochain g hg).hom
  rw [hcancel]
  have hclosed : K.d 1 2 (windingIntegerCochain g hg).hom = 0 := by
    exact windingIntegerCochainElement_closed g hg
  rw [hclosed, map_zero]

/-- The degree-zero cone cochain whose differential is the relative winding cocycle of the
restriction of a nowhere-zero ambient function. -/
def rawRelativeWindingUnitPrimitive :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).X
      (ComplexShape.embeddingUpNat.f 0) :=
  (CochainComplex.mappingCone.inl (relativeCochainRestrictionInt ℚ X)).v
    (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 0)
    (by change (1 : ℤ) + -1 = 0; norm_num)
    (ambientExtendedWindingIntegerCochainElement (X := X) g hg)

/-- Restricting the ambient literal winding cochain gives the literal winding cochain of the
restricted function. -/
lemma relativeCochainRestrictionInt_ambientExtendedWindingIntegerCochainElement :
    (relativeCochainRestrictionInt ℚ X).f (ComplexShape.embeddingUpNat.f 1)
      (ambientExtendedWindingIntegerCochainElement (X := X) g hg) =
    extendedWindingIntegerCochainElement (X := X) (g.comp (topMap X.map))
      (fun x => hg (X.map x)) := by
  let KA := (singularChains X.fst).linearDualCochainComplex
  let KS := ((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex
  let eA := KA.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
  let eS := KS.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
  apply (ModuleCat.mono_iff_injective eS.hom).mp inferInstance
  rw [show (relativeCochainRestrictionInt ℚ X).f (ComplexShape.embeddingUpNat.f 1) =
      eA.hom ≫ (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj X).hom).f 1 ≫
        eS.inv by
    exact HomologicalComplex.extendMap_f
      (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj X).hom)
      ComplexShape.embeddingUpNat rfl]
  change eS.hom (eS.inv
      ((HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj X).hom).f 1
        (eA.hom (ambientExtendedWindingIntegerCochainElement (X := X) g hg)))) =
    eS.hom (extendedWindingIntegerCochainElement (X := X) (g.comp (topMap X.map))
      (fun x => hg (X.map x)))
  rw [eS.inv_hom_id_apply]
  rw [extendedWindingIntegerCochainElement_transport]
  change (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj X).hom).f 1
      (eA.hom (eA.inv ((windingIntegerCochain g hg).hom))) =
    pairWindingIntegerCochainElement (X := X) (g.comp (topMap X.map))
      (fun x => hg (X.map x))
  have hcancel : eA.hom (eA.inv ((windingIntegerCochain g hg).hom)) =
      (windingIntegerCochain g hg).hom :=
    ConcreteCategory.congr_hom eA.inv_hom_id (windingIntegerCochain g hg).hom
  rw [hcancel]
  rw [HomologicalComplex.linearDualMap_f]
  apply LinearMap.ext
  intro z
  change (windingIntegerCochain g hg).hom
      ((((chainPairFunctor ℚ).obj X).hom.f 1).hom z) =
    (windingIntegerCochain (g.comp (topMap X.map)) (fun x => hg (X.map x))).hom z
  have hnat := chainComplexMap_comp_windingIntegerCochain
    g hg X.map (fun x => hg (X.map x))
  change ((chainPairFunctor ℚ).obj X).hom.f 1 ≫ windingIntegerCochain g hg =
    windingIntegerCochain (g.comp (topMap X.map)) (fun x => hg (X.map x)) at hnat
  exact ConcreteCategory.congr_hom hnat z

/-- The relative winding cochain of a function that is nonzero on the ambient space is the
differential of the displayed ambient primitive. -/
lemma mappingCone_d_rawRelativeWindingUnitPrimitive :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
      (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
      (rawRelativeWindingUnitPrimitive (X := X) g hg) =
    rawRelativeWindingCochain (X := X) (g.comp (topMap X.map)) (fun x => hg (X.map x)) := by
  change (((CochainComplex.mappingCone.inl (relativeCochainRestrictionInt ℚ X)).v
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 0)
      (by change (1 : ℤ) + -1 = 0; norm_num) ≫ (CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ X)).d
          (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)).hom
      (ambientExtendedWindingIntegerCochainElement (X := X) g hg)) = _
  rw [CochainComplex.mappingCone.inl_v_d (relativeCochainRestrictionInt ℚ X)
    (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 0)
    (ComplexShape.embeddingUpNat.f 2)
    (by change (1 : ℤ) + -1 = 0; norm_num)
    (by change (2 : ℤ) + -1 = 1; norm_num)]
  let D := ((SingularChainComplex ℚ X.fst).linearDualCochainComplex.extend
    ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 1)
      (ComplexShape.embeddingUpNat.f 2)
  let ι := (CochainComplex.mappingCone.inl (relativeCochainRestrictionInt ℚ X)).v
    (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
    (by change (2 : ℤ) + -1 = 1; norm_num)
  let A := (relativeCochainRestrictionInt ℚ X).f (ComplexShape.embeddingUpNat.f 1) ≫
    (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
      (ComplexShape.embeddingUpNat.f 1)
  let B := D ≫ ι
  change A.hom (ambientExtendedWindingIntegerCochainElement (X := X) g hg) -
    B.hom (ambientExtendedWindingIntegerCochainElement (X := X) g hg) = _
  have hclosed : D (ambientExtendedWindingIntegerCochainElement (X := X) g hg) = 0 := by
    exact ambientExtendedWindingIntegerCochainElement_closed (X := X) g hg
  have hB : B.hom (ambientExtendedWindingIntegerCochainElement (X := X) g hg) = 0 := by
    change ι.hom (D (ambientExtendedWindingIntegerCochainElement (X := X) g hg)) = 0
    rw [hclosed, map_zero]
  rw [hB, sub_zero]
  change (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
      (ComplexShape.embeddingUpNat.f 1)
      ((relativeCochainRestrictionInt ℚ X).f (ComplexShape.embeddingUpNat.f 1)
        (ambientExtendedWindingIntegerCochainElement (X := X) g hg)) = _
  rw [relativeCochainRestrictionInt_ambientExtendedWindingIntegerCochainElement]
  exact (rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement
    (X := X) (g.comp (topMap X.map)) (fun x => hg (X.map x))).symm

/-- The completely explicit overlap primitive when two normal coordinates differ by an ambient
unit.  It is the ambient-unit primitive minus the principal-log branch-jump primitive. -/
def rawRelativeWindingCoordinateTransitionPrimitive
    (g : C(X.snd, ℂ)) (u : C(X.fst, ℂ)) (k : C(X.snd, ℂ))
    (hg : ∀ x, g x ≠ 0) (hu : ∀ x, u x ≠ 0) (hk : ∀ x, k x ≠ 0)
    (hmul : ∀ x, k x = g x * (u.comp (topMap X.map)) x) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).X
      (ComplexShape.embeddingUpNat.f 0) :=
  rawRelativeWindingUnitPrimitive (X := X) u hu -
    rawRelativeWindingTransitionPrimitive (X := X) g (u.comp (topMap X.map)) k hg
      (fun x => hu (X.map x)) hk hmul

/-- On an overlap, the two normal-coordinate winding cochains differ by the cone differential
of `rawRelativeWindingCoordinateTransitionPrimitive`. -/
theorem rawRelativeWindingCochain_coordinateTransition
    (g₀ : C(X.snd, ℂ)) (u : C(X.fst, ℂ)) (k : C(X.snd, ℂ))
    (hg₀ : ∀ x, g₀ x ≠ 0) (hu : ∀ x, u x ≠ 0) (hk : ∀ x, k x ≠ 0)
    (hmul : ∀ x, k x = g₀ x * (u.comp (topMap X.map)) x) :
    rawRelativeWindingCochain (X := X) k hk =
      rawRelativeWindingCochain (X := X) g₀ hg₀ +
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
        (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
        (rawRelativeWindingCoordinateTransitionPrimitive (X := X) g₀ u k hg₀ hu hk hmul) := by
  rw [rawRelativeWindingCochain_mul_eq_add_sub_coboundary
    g₀ (u.comp (topMap X.map)) k hg₀ (fun x => hu (X.map x)) hk hmul,
    ← mappingCone_d_rawRelativeWindingUnitPrimitive (X := X) u hu]
  dsimp [rawRelativeWindingCoordinateTransitionPrimitive]
  simp only [map_sub]
  abel

end ChernWinding
