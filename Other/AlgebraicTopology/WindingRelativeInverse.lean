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

public import Other.AlgebraicTopology.WindingRelativeUnitBoundary

/-!
# The explicit relative winding inverse formula

The product formula for winding cochains applied to `g * g⁻¹ = 1` leaves the winding
cochain of the constant function `1`.  In a relative cone that cochain need not be discarded
definitionally.  Instead it is the boundary of the literal ambient constant-one winding
cochain.  Combining these two displayed primitives gives the inverse identity with no chosen
cochain and no equality hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology.Singular

namespace ChernWinding

variable {X : TopPair.{0}}

/-- The constant-one function on a topological space, as a continuous map to `ℂ`. -/
def constantOneContinuousMap (Y : TopCat.{0}) : C(Y, ℂ) :=
  ⟨fun _ => 1, continuous_const⟩

@[simp]
lemma constantOneContinuousMap_apply (Y : TopCat.{0}) (y : Y) :
    constantOneContinuousMap Y y = 1 :=
  rfl

lemma constantOneContinuousMap_ne_zero (Y : TopCat.{0}) :
    ∀ y, constantOneContinuousMap Y y ≠ 0 := by
  intro y
  simp

/-- The constant-zero logarithm of `constantOneContinuousMap`. -/
def constantZeroContinuousMap (Y : TopCat.{0}) : C(Y, ℂ) :=
  ⟨fun _ => 0, continuous_const⟩

/-- The integer winding index of the literal constant-one function is zero.  This is proved
from the defining principal-log formula, rather than imposed as a normalization of the
noncomputable choice occurring in `windingIndex`. -/
lemma windingIndex_constantOne_eq_zero (Y : TopCat.{0})
    (sigma : _) :
    windingIndex (constantOneContinuousMap Y) (constantOneContinuousMap_ne_zero Y) sigma = 0 := by
  let one := constantOneContinuousMap Y
  let zero := constantZeroContinuousMap Y
  have hincrement := simplexIncrement_of_exp one zero (fun _ => one_ne_zero)
    (fun _ => by
      change Complex.exp 0 = 1
      exact Complex.exp_zero) sigma
  have hformula := simplexIncrement_eq_pointLog_add_windingIndex one
    (fun _ => one_ne_zero) sigma
  have hincrement_zero : simplexIncrement one (fun _ => one_ne_zero) sigma = 0 := by
    rw [hincrement]
    change (0 : ℂ) - 0 = 0
    ring
  have hpointLog_zero :
      pointLog one (simplexMap sigma (stdSimplex.vertex 1)) -
        pointLog one (simplexMap sigma (stdSimplex.vertex 0)) = 0 := by
    change Complex.log 1 - Complex.log 1 = 0
    ring
  have hmul :
      ((windingIndex one (fun _ => one_ne_zero) sigma : ℤ) : ℂ) * twoPiI = 0 := by
    rw [hincrement_zero, hpointLog_zero, zero_add] at hformula
    exact hformula.symm
  have hcast : ((windingIndex one (fun _ => one_ne_zero) sigma : ℤ) : ℂ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_right twoPiI_ne_zero
  exact_mod_cast hcast

/-- The literal rational winding cochain of the constant-one function is zero. -/
lemma windingIntegerCochain_constantOne_eq_zero (Y : TopCat.{0}) :
    windingIntegerCochain (constantOneContinuousMap Y)
      (constantOneContinuousMap_ne_zero Y) = 0 := by
  refine SSet.chainComplex_hom_ext fun sigma => ?_
  rw [comp_zero]
  rw [ιChainComplex_comp_windingIntegerCochain]
  rw [windingIndex_constantOne_eq_zero Y sigma]
  ext
  simp [scalarHomRat, LinearMap.toSpanSingleton]

/-- The pointwise inverse of a nowhere-zero continuous complex-valued function. -/
def nowhereZeroContinuousMapInv {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ x, g x ≠ 0) :
    C(Y, ℂ) :=
  ⟨fun x => (g x)⁻¹, g.continuous.inv₀ hg⟩

@[simp]
lemma nowhereZeroContinuousMapInv_apply {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ x, g x ≠ 0)
    (x : Y) : nowhereZeroContinuousMapInv g hg x = (g x)⁻¹ :=
  rfl

lemma nowhereZeroContinuousMapInv_ne_zero {Y : TopCat.{0}}
    (g : C(Y, ℂ)) (hg : ∀ x, g x ≠ 0) :
    ∀ x, nowhereZeroContinuousMapInv g hg x ≠ 0 := by
  intro x
  exact inv_ne_zero (hg x)

/-- The ordinary integer winding cochain of the pointwise inverse, with its explicit
principal-log correction. -/
theorem windingIntegerCochain_inv_eq_neg_add_coboundary
    {Y : TopCat.{0}} (g : C(Y, ℂ)) (hg : ∀ x, g x ≠ 0) :
    windingIntegerCochain (nowhereZeroContinuousMapInv g hg)
        (nowhereZeroContinuousMapInv_ne_zero g hg) =
      -windingIntegerCochain g hg +
        (singularChains Y).d 1 0 ≫
          pointLogProductDefectVertexCochain g
            (nowhereZeroContinuousMapInv g hg)
            (constantOneContinuousMap Y) hg
            (nowhereZeroContinuousMapInv_ne_zero g hg)
            (constantOneContinuousMap_ne_zero Y) (fun x => by simp [hg x]) := by
  let gInv := nowhereZeroContinuousMapInv g hg
  let hgInv : ∀ x, gInv x ≠ 0 :=
    nowhereZeroContinuousMapInv_ne_zero g hg
  let one := constantOneContinuousMap Y
  let hone : ∀ x, one x ≠ 0 := fun _ => one_ne_zero
  let hmul : ∀ x, one x = g x * gInv x := fun x => by simp [one, gInv, hg x]
  have hproduct := windingIntegerCochain_mul_eq_add_sub_coboundary
    g gInv one hg hgInv hone hmul
  rw [windingIntegerCochain_constantOne_eq_zero] at hproduct
  have hinverse :
      windingIntegerCochain gInv hgInv =
        -windingIntegerCochain g hg +
          (singularChains Y).d 1 0 ≫
            pointLogProductDefectVertexCochain g gInv one hg hgInv hone hmul := by
    symm
    calc
      _ = (-windingIntegerCochain g hg +
          (singularChains Y).d 1 0 ≫
            pointLogProductDefectVertexCochain g gInv one hg hgInv hone hmul) + 0 := by
        simp
      _ = windingIntegerCochain gInv hgInv := by
        rw [hproduct]
        abel
  simpa [gInv, one] using hinverse

/-- The explicit pair-overlap vertex correction when `a * b = 1` and a second normal
coordinate is `n₁ * b`.  This is the correction needed on the `12` overlap of the coordinate
cover: the inverse-transition defect minus the normal-coordinate product defect. -/
def windingIntegerCochainInverseProductCorrection
    {Y : TopCat.{0}} (a b n₁ n₂ : C(Y, ℂ))
    (ha : ∀ x, a x ≠ 0) (hb : ∀ x, b x ≠ 0)
    (hn₁ : ∀ x, n₁ x ≠ 0) (hn₂ : ∀ x, n₂ x ≠ 0)
    (hab : ∀ x, constantOneContinuousMap Y x = a x * b x)
    (hnorm : ∀ x, n₂ x = n₁ x * b x) :
    (singularChains Y).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  pointLogProductDefectVertexCochain a b (constantOneContinuousMap Y)
      ha hb (constantOneContinuousMap_ne_zero Y) hab -
    pointLogProductDefectVertexCochain n₁ b n₂ hn₁ hb hn₂ hnorm

/-- Pullback of the inverse-product correction is the correction built from the four pulled-back
functions. -/
theorem chainComplexMap_comp_windingIntegerCochainInverseProductCorrection
    {Y Y' : TopCat.{0}} (f : Y' ⟶ Y) (a b n₁ n₂ : C(Y, ℂ))
    (ha : ∀ y, a y ≠ 0) (hb : ∀ y, b y ≠ 0)
    (hn₁ : ∀ y, n₁ y ≠ 0) (hn₂ : ∀ y, n₂ y ≠ 0)
    (hab : ∀ y, constantOneContinuousMap Y y = a y * b y)
    (hnorm : ∀ y, n₂ y = n₁ y * b y)
    (haf : ∀ y, (a.comp (topMap f)) y ≠ 0)
    (hbf : ∀ y, (b.comp (topMap f)) y ≠ 0)
    (hn₁f : ∀ y, (n₁.comp (topMap f)) y ≠ 0)
    (hn₂f : ∀ y, (n₂.comp (topMap f)) y ≠ 0)
    (habf : ∀ y, (constantOneContinuousMap Y).comp (topMap f) y =
      (a.comp (topMap f)) y * (b.comp (topMap f)) y)
    (hnormf : ∀ y, (n₂.comp (topMap f)) y =
      (n₁.comp (topMap f)) y * (b.comp (topMap f)) y) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0 ≫
        windingIntegerCochainInverseProductCorrection a b n₁ n₂
          ha hb hn₁ hn₂ hab hnorm =
      pointLogProductDefectVertexCochain
          (a.comp (topMap f)) (b.comp (topMap f))
          ((constantOneContinuousMap Y).comp (topMap f)) haf hbf
          (fun _ ↦ one_ne_zero) habf -
        pointLogProductDefectVertexCochain
          (n₁.comp (topMap f)) (b.comp (topMap f)) (n₂.comp (topMap f))
          hn₁f hbf hn₂f hnormf := by
  dsimp only [windingIntegerCochainInverseProductCorrection]
  rw [Preadditive.comp_sub,
    chainComplexMap_comp_pointLogProductDefectVertexCochain f a b
      (constantOneContinuousMap Y) ha hb (constantOneContinuousMap_ne_zero Y) hab
      haf hbf (fun _ ↦ one_ne_zero) habf,
    chainComplexMap_comp_pointLogProductDefectVertexCochain f n₁ b n₂
      hn₁ hb hn₂ hnorm hn₁f hbf hn₂f hnormf]

/-- Equality of the four functions transports the inverse-product correction. -/
theorem windingIntegerCochainInverseProductCorrection_congr
    {Y : TopCat.{0}} (a b n₁ n₂ a' b' n₁' n₂' : C(Y, ℂ))
    (ha : ∀ y, a y ≠ 0) (hb : ∀ y, b y ≠ 0)
    (hn₁ : ∀ y, n₁ y ≠ 0) (hn₂ : ∀ y, n₂ y ≠ 0)
    (ha' : ∀ y, a' y ≠ 0) (hb' : ∀ y, b' y ≠ 0)
    (hn₁' : ∀ y, n₁' y ≠ 0) (hn₂' : ∀ y, n₂' y ≠ 0)
    (hab : ∀ y, constantOneContinuousMap Y y = a y * b y)
    (hnorm : ∀ y, n₂ y = n₁ y * b y)
    (hab' : ∀ y, constantOneContinuousMap Y y = a' y * b' y)
    (hnorm' : ∀ y, n₂' y = n₁' y * b' y)
    (haa' : a = a') (hbb' : b = b') (hn₁n₁' : n₁ = n₁') (hn₂n₂' : n₂ = n₂') :
    windingIntegerCochainInverseProductCorrection a b n₁ n₂
        ha hb hn₁ hn₂ hab hnorm =
      windingIntegerCochainInverseProductCorrection a' b' n₁' n₂'
        ha' hb' hn₁' hn₂' hab' hnorm' := by
  subst a'
  subst b'
  subst n₁'
  subst n₂'
  rfl

/-- Pullback followed by replacement of the four pulled-back functions by extensionally equal
functions.  This combines the two bookkeeping steps needed on a Čech triple intersection. -/
theorem chainComplexMap_comp_windingIntegerCochainInverseProductCorrection_congr
    {Y Y' : TopCat.{0}} (f : Y' ⟶ Y) (a b n₁ n₂ : C(Y, ℂ))
    (ha : ∀ y, a y ≠ 0) (hb : ∀ y, b y ≠ 0)
    (hn₁ : ∀ y, n₁ y ≠ 0) (hn₂ : ∀ y, n₂ y ≠ 0)
    (hab : ∀ y, constantOneContinuousMap Y y = a y * b y)
    (hnorm : ∀ y, n₂ y = n₁ y * b y)
    (haf : ∀ y, (a.comp (topMap f)) y ≠ 0)
    (hbf : ∀ y, (b.comp (topMap f)) y ≠ 0)
    (hn₁f : ∀ y, (n₁.comp (topMap f)) y ≠ 0)
    (hn₂f : ∀ y, (n₂.comp (topMap f)) y ≠ 0)
    (habf : ∀ y, (constantOneContinuousMap Y).comp (topMap f) y =
      (a.comp (topMap f)) y * (b.comp (topMap f)) y)
    (hnormf : ∀ y, (n₂.comp (topMap f)) y =
      (n₁.comp (topMap f)) y * (b.comp (topMap f)) y)
    (a' b' n₁' n₂' : C(Y', ℂ))
    (ha' : ∀ y, a' y ≠ 0) (hb' : ∀ y, b' y ≠ 0)
    (hn₁' : ∀ y, n₁' y ≠ 0) (hn₂' : ∀ y, n₂' y ≠ 0)
    (hab' : ∀ y, constantOneContinuousMap Y' y = a' y * b' y)
    (hnorm' : ∀ y, n₂' y = n₁' y * b' y)
    (haa' : a.comp (topMap f) = a') (hbb' : b.comp (topMap f) = b')
    (hn₁n₁' : n₁.comp (topMap f) = n₁')
    (hn₂n₂' : n₂.comp (topMap f) = n₂') :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0 ≫
        windingIntegerCochainInverseProductCorrection a b n₁ n₂
          ha hb hn₁ hn₂ hab hnorm =
      windingIntegerCochainInverseProductCorrection a' b' n₁' n₂'
        ha' hb' hn₁' hn₂' hab' hnorm' := by
  rw [chainComplexMap_comp_windingIntegerCochainInverseProductCorrection f a b n₁ n₂
    ha hb hn₁ hn₂ hab hnorm haf hbf hn₁f hn₂f habf hnormf]
  dsimp only [windingIntegerCochainInverseProductCorrection]
  apply congrArg₂ (fun x y ↦ x - y)
  · exact pointLogProductDefectVertexCochain_congr
      (a.comp (topMap f)) (b.comp (topMap f))
      ((constantOneContinuousMap Y).comp (topMap f)) a' b'
      (constantOneContinuousMap Y') haf hbf (fun _ ↦ one_ne_zero)
      ha' hb' (constantOneContinuousMap_ne_zero _) habf hab'
      haa' hbb' (by ext y; rfl)
  · exact pointLogProductDefectVertexCochain_congr
      (n₁.comp (topMap f)) (b.comp (topMap f)) (n₂.comp (topMap f))
      n₁' b' n₂' hn₁f hbf hn₂f hn₁' hb' hn₂'
      hnormf hnorm' hn₁n₁' hbb' hn₂n₂'

/-- The `12`-overlap identity at the level of literal integer singular cochains. -/
theorem windingIntegerCochain_add_normalDifference_eq_coboundary
    {Y : TopCat.{0}} (a b n₁ n₂ : C(Y, ℂ))
    (ha : ∀ x, a x ≠ 0) (hb : ∀ x, b x ≠ 0)
    (hn₁ : ∀ x, n₁ x ≠ 0) (hn₂ : ∀ x, n₂ x ≠ 0)
    (hab : ∀ x, constantOneContinuousMap Y x = a x * b x)
    (hnorm : ∀ x, n₂ x = n₁ x * b x) :
    windingIntegerCochain a ha + windingIntegerCochain n₂ hn₂ -
        windingIntegerCochain n₁ hn₁ =
      (singularChains Y).d 1 0 ≫
        windingIntegerCochainInverseProductCorrection
          a b n₁ n₂ ha hb hn₁ hn₂ hab hnorm := by
  have hinv := windingIntegerCochain_mul_eq_add_sub_coboundary
    a b (constantOneContinuousMap Y) ha hb
      (constantOneContinuousMap_ne_zero Y) hab
  have hnorm' := windingIntegerCochain_mul_eq_add_sub_coboundary
    n₁ b n₂ hn₁ hb hn₂ hnorm
  rw [windingIntegerCochain_constantOne_eq_zero] at hinv
  dsimp [windingIntegerCochainInverseProductCorrection]
  rw [Preadditive.comp_sub]
  have hinv' :
      windingIntegerCochain a ha + windingIntegerCochain b hb =
        (singularChains Y).d 1 0 ≫
          pointLogProductDefectVertexCochain a b (constantOneContinuousMap Y)
            ha hb (constantOneContinuousMap_ne_zero Y) hab := by
    calc
      _ = (windingIntegerCochain a ha + windingIntegerCochain b hb -
          (singularChains Y).d 1 0 ≫
            pointLogProductDefectVertexCochain a b (constantOneContinuousMap Y)
              ha hb (constantOneContinuousMap_ne_zero Y) hab) +
          ((singularChains Y).d 1 0 ≫
            pointLogProductDefectVertexCochain a b (constantOneContinuousMap Y)
              ha hb (constantOneContinuousMap_ne_zero Y) hab) := by
        abel
      _ = _ := by rw [← hinv]; simp
  rw [hnorm']
  rw [← hinv']
  abel

/-- The explicit degree-zero relative-cone primitive for the inverse identity.  Its first
summand is the ambient primitive for the constant function `1`; its second summand is the
principal-log branch-jump primitive for `g * g⁻¹ = 1`. -/
def rawRelativeWindingInversePrimitive (g : C(X.snd, ℂ)) (hg : ∀ x, g x ≠ 0) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).X
      (ComplexShape.embeddingUpNat.f 0) :=
  let oneA := constantOneContinuousMap X.fst
  let oneS := constantOneContinuousMap X.snd
  let gInv := nowhereZeroContinuousMapInv g hg
  rawRelativeWindingUnitPrimitive (X := X) oneA (fun _ => one_ne_zero) +
    rawRelativeWindingTransitionPrimitive (X := X) g gInv oneS hg
      (nowhereZeroContinuousMapInv_ne_zero g hg) (fun _ => one_ne_zero)
      (fun x => by simp [oneS, gInv, hg x])

/-- The raw relative winding cochain of `g⁻¹` is the negative of that of `g`, up to the
coboundary of the completely explicit primitive above. -/
theorem rawRelativeWindingCochain_inv_eq_neg_add_coboundary
    (g : C(X.snd, ℂ)) (hg : ∀ x, g x ≠ 0) :
    rawRelativeWindingCochain (X := X) (nowhereZeroContinuousMapInv g hg)
        (nowhereZeroContinuousMapInv_ne_zero g hg) =
      -rawRelativeWindingCochain (X := X) g hg +
        (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
          (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
          (rawRelativeWindingInversePrimitive (X := X) g hg) := by
  let oneA := constantOneContinuousMap X.fst
  let oneS := constantOneContinuousMap X.snd
  let gInv := nowhereZeroContinuousMapInv g hg
  let hgInv : ∀ x, gInv x ≠ 0 := nowhereZeroContinuousMapInv_ne_zero g hg
  let honeA : ∀ x, oneA x ≠ 0 := fun _ => one_ne_zero
  let honeS : ∀ x, oneS x ≠ 0 := fun _ => one_ne_zero
  let hmul : ∀ x, oneS x = g x * gInv x := fun x => by
    simp [oneS, gInv, hg x]
  have hproduct := rawRelativeWindingCochain_mul_eq_add_sub_coboundary
    (X := X) g gInv oneS hg hgInv honeS hmul
  have honeRestriction : oneA.comp (topMap X.map) = oneS := by
    ext x
    rfl
  have hunit := mappingCone_d_rawRelativeWindingUnitPrimitive (X := X) oneA honeA
  have hunit' :
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
          (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
          (rawRelativeWindingUnitPrimitive (X := X) oneA honeA) =
        rawRelativeWindingCochain (X := X) oneS honeS := by
    simpa [honeRestriction] using hunit
  rw [← hunit'] at hproduct
  dsimp [rawRelativeWindingInversePrimitive]
  simp only [map_add]
  rw [hproduct]
  abel

end ChernWinding
