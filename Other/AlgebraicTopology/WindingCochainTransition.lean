/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.WindingRelativeCocycle

/-!
# The explicit transition cochain for winding cocycles

The local normal coordinates of a divisor differ on an overlap by multiplication by a
nowhere-zero transition function.  Winding is additive only up to the jump of the chosen
principal logarithm.  This file makes that correction completely literal: it is an
integer-valued singular `0`-cochain, and its coboundary is the discrepancy between the three
integer winding cochains.

Thus the usual formula

`wind (g * h) = wind g + wind h - d(branchJump(g,h))`

is an equality of raw rational singular cochains, rather than merely an equality after passing
to cohomology.  This is the overlap formula needed to glue the two normal-coordinate winding
cocycles for the coordinate hyperplane in `ℙ²`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology.Singular

namespace ChernWinding

variable {Y : TopCat.{0}}

/-- The integer by which the principal logarithm fails to respect a pointwise product. -/
def pointLogProductDefect (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) (y : Y) : ℤ :=
  (show ∃ n : ℤ, pointLog k y = pointLog g y + pointLog h y + (n : ℂ) * twoPiI by
    apply Complex.exp_eq_exp_iff_exists_int.mp
    rw [exp_pointLog k hk, Complex.exp_add, exp_pointLog g hg, exp_pointLog h hh, hmul]).choose

/-- The defining branch-jump equation. -/
theorem pointLogProductDefect_spec (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) (y : Y) :
    pointLog k y = pointLog g y + pointLog h y +
      (pointLogProductDefect g h k hg hh hk hmul y : ℂ) * twoPiI :=
  (show ∃ n : ℤ, pointLog k y = pointLog g y + pointLog h y + (n : ℂ) * twoPiI by
    apply Complex.exp_eq_exp_iff_exists_int.mp
    rw [exp_pointLog k hk, Complex.exp_add, exp_pointLog g hg, exp_pointLog h hh, hmul]).choose_spec

/-- The branch-jump, regarded as a literal rational singular `0`-cochain. -/
def pointLogProductDefectVertexCochain (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) :
    (singularChains Y).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  Limits.Cofan.IsColimit.desc
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 0)
    fun v => scalarHomRat ((pointLogProductDefect g h k hg hh hk hmul
      (simplexMap v default) : ℤ) : ℚ)

@[reassoc]
theorem ιChainComplex_comp_pointLogProductDefectVertexCochain
    (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y)
    (v : (TopCat.toSSet.obj Y) _⦋0⦌) :
    (TopCat.toSSet.obj Y).ιChainComplex v ≫
      pointLogProductDefectVertexCochain g h k hg hh hk hmul =
        scalarHomRat ((pointLogProductDefect g h k hg hh hk hmul
          (simplexMap v default) : ℤ) : ℚ) :=
  Limits.Cofan.IsColimit.fac
    (SSet.isColimitChainComplexXCofan (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) 0) _ v

/-- Equality of the three functions transports the literal branch-defect vertex cochain.
The nonvanishing and product witnesses are propositions, hence proof-irrelevant. -/
theorem pointLogProductDefectVertexCochain_congr
    (g h k g' h' k' : C(Y, ℂ))
    (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hg' : ∀ y, g' y ≠ 0) (hh' : ∀ y, h' y ≠ 0) (hk' : ∀ y, k' y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) (hmul' : ∀ y, k' y = g' y * h' y)
    (hgg' : g = g') (hhh' : h = h') (hkk' : k = k') :
    pointLogProductDefectVertexCochain g h k hg hh hk hmul =
      pointLogProductDefectVertexCochain g' h' k' hg' hh' hk' hmul' := by
  subst g'
  subst h'
  subst k'
  rfl

/-- Pullback of the literal branch-defect vertex cochain is the branch-defect cochain of the
three pulled-back functions. -/
theorem chainComplexMap_comp_pointLogProductDefectVertexCochain
    {Y' : TopCat.{0}} (f : Y' ⟶ Y) (g h k : C(Y, ℂ))
    (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y)
    (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0)
    (hhf : ∀ y, (h.comp (topMap f)) y ≠ 0)
    (hkf : ∀ y, (k.comp (topMap f)) y ≠ 0)
    (hmulf : ∀ y, (k.comp (topMap f)) y =
      (g.comp (topMap f)) y * (h.comp (topMap f)) y) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0 ≫
        pointLogProductDefectVertexCochain g h k hg hh hk hmul =
      pointLogProductDefectVertexCochain
        (g.comp (topMap f)) (h.comp (topMap f)) (k.comp (topMap f))
        hgf hhf hkf hmulf := by
  refine SSet.chainComplex_hom_ext fun v ↦ ?_
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    ιChainComplex_comp_pointLogProductDefectVertexCochain,
    ιChainComplex_comp_pointLogProductDefectVertexCochain]
  rfl

/-- The four branch corrections associated to a product and its inverse product satisfy the
alternating Čech identity.  This is the pointwise integer calculation behind the triple-overlap
compatibility for inverse local defining equations. -/
theorem pointLogProductDefect_alternating_inverse
    (g01 g12 g02 i01 i12 i02 one : C(Y, ℂ))
    (hg01 : ∀ y, g01 y ≠ 0) (hg12 : ∀ y, g12 y ≠ 0) (hg02 : ∀ y, g02 y ≠ 0)
    (hi01 : ∀ y, i01 y ≠ 0) (hi12 : ∀ y, i12 y ≠ 0) (hi02 : ∀ y, i02 y ≠ 0)
    (hone : ∀ y, one y ≠ 0)
    (hprod : ∀ y, g02 y = g01 y * g12 y)
    (hinv01 : ∀ y, one y = g01 y * i01 y)
    (hinv12 : ∀ y, one y = g12 y * i12 y)
    (hinv02 : ∀ y, one y = g02 y * i02 y)
    (hinvprod : ∀ y, i02 y = i01 y * i12 y)
    (honeLog : ∀ y, pointLog one y = 0) (y : Y) :
    pointLogProductDefect g01 i01 one hg01 hi01 hone hinv01 y -
        pointLogProductDefect g02 i02 one hg02 hi02 hone hinv02 y +
      (pointLogProductDefect g12 i12 one hg12 hi12 hone hinv12 y -
        pointLogProductDefect i01 i12 i02 hi01 hi12 hi02 hinvprod y) =
      pointLogProductDefect g01 g12 g02 hg01 hg12 hg02 hprod y := by
  suffices hcast :
      ((pointLogProductDefect g01 i01 one hg01 hi01 hone hinv01 y -
          pointLogProductDefect g02 i02 one hg02 hi02 hone hinv02 y +
        (pointLogProductDefect g12 i12 one hg12 hi12 hone hinv12 y -
          pointLogProductDefect i01 i12 i02 hi01 hi12 hi02 hinvprod y) : ℤ) : ℂ) =
        (pointLogProductDefect g01 g12 g02 hg01 hg12 hg02 hprod y : ℂ) by
    exact_mod_cast hcast
  apply mul_right_cancel₀ twoPiI_ne_zero
  have h01 := pointLogProductDefect_spec g01 i01 one hg01 hi01 hone hinv01 y
  have h12 := pointLogProductDefect_spec g12 i12 one hg12 hi12 hone hinv12 y
  have h02 := pointLogProductDefect_spec g02 i02 one hg02 hi02 hone hinv02 y
  have hip := pointLogProductDefect_spec i01 i12 i02 hi01 hi12 hi02 hinvprod y
  have hp := pointLogProductDefect_spec g01 g12 g02 hg01 hg12 hg02 hprod y
  rw [honeLog y] at h01 h12 h02
  push_cast
  linear_combination -h01 + h02 - h12 + hip + hp

/-- Cochain form of `pointLogProductDefect_alternating_inverse`.  All four corrections are
literal vertex cochains, so no representative or branch-independence hypothesis is involved. -/
theorem pointLogProductDefectVertexCochain_alternating_inverse
    (g01 g12 g02 i01 i12 i02 one : C(Y, ℂ))
    (hg01 : ∀ y, g01 y ≠ 0) (hg12 : ∀ y, g12 y ≠ 0) (hg02 : ∀ y, g02 y ≠ 0)
    (hi01 : ∀ y, i01 y ≠ 0) (hi12 : ∀ y, i12 y ≠ 0) (hi02 : ∀ y, i02 y ≠ 0)
    (hone : ∀ y, one y ≠ 0)
    (hprod : ∀ y, g02 y = g01 y * g12 y)
    (hinv01 : ∀ y, one y = g01 y * i01 y)
    (hinv12 : ∀ y, one y = g12 y * i12 y)
    (hinv02 : ∀ y, one y = g02 y * i02 y)
    (hinvprod : ∀ y, i02 y = i01 y * i12 y)
    (honeLog : ∀ y, pointLog one y = 0) :
    pointLogProductDefectVertexCochain g01 i01 one hg01 hi01 hone hinv01 -
        pointLogProductDefectVertexCochain g02 i02 one hg02 hi02 hone hinv02 +
      (pointLogProductDefectVertexCochain g12 i12 one hg12 hi12 hone hinv12 -
        pointLogProductDefectVertexCochain i01 i12 i02 hi01 hi12 hi02 hinvprod) =
      pointLogProductDefectVertexCochain g01 g12 g02 hg01 hg12 hg02 hprod := by
  refine SSet.chainComplex_hom_ext fun v ↦ ?_
  simp only [Preadditive.comp_add, Preadditive.comp_sub,
    ιChainComplex_comp_pointLogProductDefectVertexCochain]
  have h := pointLogProductDefect_alternating_inverse
    g01 g12 g02 i01 i12 i02 one hg01 hg12 hg02 hi01 hi12 hi02 hone
    hprod hinv01 hinv12 hinv02 hinvprod honeLog (simplexMap v default)
  ext
  have hq :
    ((pointLogProductDefect g01 i01 one hg01 hi01 hone hinv01
          (simplexMap v default) : ℤ) : ℚ) -
        (pointLogProductDefect g02 i02 one hg02 hi02 hone hinv02
          (simplexMap v default) : ℚ) +
      ((pointLogProductDefect g12 i12 one hg12 hi12 hone hinv12
          (simplexMap v default) : ℚ) -
        (pointLogProductDefect i01 i12 i02 hi01 hi12 hi02 hinvprod
          (simplexMap v default) : ℚ)) =
      (pointLogProductDefect g01 g12 g02 hg01 hg12 hg02 hprod
        (simplexMap v default) : ℚ) := by
    exact_mod_cast h
  simpa [scalarHomRat, LinearMap.toSpanSingleton] using hq

/-- The pointwise integer identity behind the raw cochain transition formula. -/
theorem windingIndex_mul_eq (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) (σ : (TopCat.toSSet.obj Y) _⦋1⦌) :
    windingIndex k hk σ = windingIndex g hg σ + windingIndex h hh σ -
      (pointLogProductDefect g h k hg hh hk hmul
        (simplexMap σ (stdSimplex.vertex 1)) -
      pointLogProductDefect g h k hg hh hk hmul
        (simplexMap σ (stdSimplex.vertex 0))) := by
  suffices hcast : (windingIndex k hk σ : ℂ) =
      ((windingIndex g hg σ + windingIndex h hh σ -
        (pointLogProductDefect g h k hg hh hk hmul
          (simplexMap σ (stdSimplex.vertex 1)) -
        pointLogProductDefect g h k hg hh hk hmul
          (simplexMap σ (stdSimplex.vertex 0))) : ℤ) : ℂ) by
    exact_mod_cast hcast
  apply mul_right_cancel₀ twoPiI_ne_zero
  calc
    (windingIndex k hk σ : ℂ) * twoPiI =
        simplexIncrement k hk σ -
          (pointLog k (simplexMap σ (stdSimplex.vertex 1)) -
            pointLog k (simplexMap σ (stdSimplex.vertex 0))) := by
      rw [simplexIncrement_eq_pointLog_add_windingIndex k hk σ]
      ring
    _ = (simplexIncrement g hg σ -
          (pointLog g (simplexMap σ (stdSimplex.vertex 1)) -
            pointLog g (simplexMap σ (stdSimplex.vertex 0)))) +
        (simplexIncrement h hh σ -
          (pointLog h (simplexMap σ (stdSimplex.vertex 1)) -
            pointLog h (simplexMap σ (stdSimplex.vertex 0)))) -
        ((pointLogProductDefect g h k hg hh hk hmul
            (simplexMap σ (stdSimplex.vertex 1)) : ℂ) -
          (pointLogProductDefect g h k hg hh hk hmul
            (simplexMap σ (stdSimplex.vertex 0)) : ℂ)) * twoPiI := by
      rw [simplexIncrement_mul g h k hg hh hk hmul σ,
        pointLogProductDefect_spec g h k hg hh hk hmul
          (simplexMap σ (stdSimplex.vertex 1)),
        pointLogProductDefect_spec g h k hg hh hk hmul
          (simplexMap σ (stdSimplex.vertex 0))]
      ring
    _ = ((windingIndex g hg σ + windingIndex h hh σ -
          (pointLogProductDefect g h k hg hh hk hmul
            (simplexMap σ (stdSimplex.vertex 1)) -
          pointLogProductDefect g h k hg hh hk hmul
            (simplexMap σ (stdSimplex.vertex 0)) : ℤ) : ℤ) : ℂ) * twoPiI := by
      rw [simplexIncrement_eq_pointLog_add_windingIndex g hg σ,
        simplexIncrement_eq_pointLog_add_windingIndex h hh σ]
      push_cast
      ring

/-- The multiplication transition formula as an equality of literal rational singular
`1`-cochains. -/
theorem windingIntegerCochain_mul_eq_add_sub_coboundary
    (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    windingIntegerCochain k hk = windingIntegerCochain g hg + windingIntegerCochain h hh -
      (singularChains Y).d 1 0 ≫
        pointLogProductDefectVertexCochain g h k hg hh hk hmul := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [Preadditive.comp_sub, Preadditive.comp_add,
    ιChainComplex_comp_windingIntegerCochain,
    ιChainComplex_comp_windingIntegerCochain,
    ιChainComplex_comp_windingIntegerCochain, ← Category.assoc,
    SSet.ιChainComplex_d, Preadditive.sum_comp]
  have scalarHomRat_zsmul (n z : ℤ) : n • scalarHomRat (z : ℚ) =
      scalarHomRat ((n * z : ℤ) : ℚ) := by
    ext
    simp [scalarHomRat, LinearMap.toSpanSingleton]
  have hterm : ∀ i : Fin 2,
      ((-1 : ℤ) ^ (i : ℕ) • (TopCat.toSSet.obj Y).ιChainComplex
          ((TopCat.toSSet.obj Y).δ i σ)) ≫
          pointLogProductDefectVertexCochain g h k hg hh hk hmul =
        scalarHomRat ((((-1 : ℤ) ^ (i : ℕ)) *
          pointLogProductDefect g h k hg hh hk hmul
            (simplexMap σ (stdSimplex.vertex (i.succAbove 0))) : ℤ) : ℚ) := by
    intro i
    rw [Preadditive.zsmul_comp,
      ιChainComplex_comp_pointLogProductDefectVertexCochain,
      simplexMap_δ_default]
    exact scalarHomRat_zsmul _ _
  simp_rw [hterm]
  have e0 : (0 : Fin 2).succAbove 0 = 1 := by decide
  have e1 : (1 : Fin 2).succAbove 0 = 0 := by decide
  rw [Fin.sum_univ_two, e0, e1]
  rw [windingIndex_mul_eq g h k hg hh hk hmul σ]
  ext
  simp [scalarHomRat, LinearMap.toSpanSingleton]
  ring

/-- The same transition identity in the literal cochain complex, rather than in the dual
description as maps out of singular chains. -/
theorem windingIntegerCochainElement_mul_eq_add_sub_coboundary
    (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    windingIntegerCochainElement k hk = windingIntegerCochainElement g hg +
      windingIntegerCochainElement h hh -
      ((singularChains Y).linearDualCochainComplex.d 0 1)
        ((pointLogProductDefectVertexCochain g h k hg hh hk hmul).hom) := by
  change (windingIntegerCochain k hk).hom = (windingIntegerCochain g hg).hom +
    (windingIntegerCochain h hh).hom -
    ((singularChains Y).d 1 0 ≫
      pointLogProductDefectVertexCochain g h k hg hh hk hmul).hom
  exact congrArg ModuleCat.Hom.hom
    (windingIntegerCochain_mul_eq_add_sub_coboundary g h k hg hh hk hmul)

variable {X : TopPair.{0}}

/-- The branch-jump cochain in the subspace factor of a relative pair. -/
def pairPointLogProductDefectVertexCochainElement
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex).X 0 :=
  (pointLogProductDefectVertexCochain g h k hg hh hk hmul).hom

/-- Extend the literal branch-jump cochain to the integer-indexed cone convention. -/
def extendedPointLogProductDefectVertexCochainElement
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).X (ComplexShape.embeddingUpNat.f 0)) :=
  (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat rfl).inv
      (pairPointLogProductDefectVertexCochainElement (X := X) g h k hg hh hk hmul)

/-- Evaluation back in the nonnegative complex recovers the displayed branch-jump cochain. -/
lemma extendedPointLogProductDefectVertexCochainElement_transport
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).hom
      (extendedPointLogProductDefectVertexCochainElement (X := X) g h k hg hh hk hmul) =
        pairPointLogProductDefectVertexCochainElement (X := X) g h k hg hh hk hmul := by
  simp [extendedPointLogProductDefectVertexCochainElement]

/-- Evaluation back in the nonnegative complex recovers the displayed winding cochain. -/
lemma extendedWindingIntegerCochainElement_transport
    (g : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) :
    (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat (i := 1) rfl).hom
      (extendedWindingIntegerCochainElement (X := X) g hg) =
        pairWindingIntegerCochainElement (X := X) g hg := by
  dsimp [extendedWindingIntegerCochainElement]
  rw [Iso.inv_hom_id_apply]
  change (LinearMap.toSpanSingleton ℚ _ (windingIntegerCochain g hg).hom) 1 =
    (windingIntegerCochain g hg).hom
  simp

/-- The raw transition identity in the subspace cochain complex of a pair. -/
theorem pairWindingIntegerCochainElement_mul_eq_add_sub_coboundary
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    pairWindingIntegerCochainElement (X := X) k hk =
      pairWindingIntegerCochainElement (X := X) g hg +
        pairWindingIntegerCochainElement (X := X) h hh -
      (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.d 0 1)
        (pairPointLogProductDefectVertexCochainElement (X := X)
          g h k hg hh hk hmul) := by
  exact windingIntegerCochainElement_mul_eq_add_sub_coboundary
    g h k hg hh hk hmul

/-- Evaluating the scalar-linear packaging of the pair winding cochain at `1` recovers the
displayed cochain itself. -/
lemma pairWindingIntegerCochainHom_apply_one (g : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) :
    (pairWindingIntegerCochainHom (X := X) g hg).hom 1 =
      pairWindingIntegerCochainElement (X := X) g hg := by
  dsimp [pairWindingIntegerCochainHom]
  rw [LinearMap.toSpanSingleton_apply]
  simp

/-- Extension by zero carries the explicit winding transition formula to the integer-indexed
cochain complex used by the relative mapping cone. -/
theorem extendedWindingIntegerCochainElement_mul_eq_add_sub_coboundary
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    extendedWindingIntegerCochainElement (X := X) k hk =
      extendedWindingIntegerCochainElement (X := X) g hg +
        extendedWindingIntegerCochainElement (X := X) h hh -
      ((((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 0)
          (ComplexShape.embeddingUpNat.f 1))
        (extendedPointLogProductDefectVertexCochainElement (X := X)
          g h k hg hh hk hmul) := by
  let K := ((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex
  let e₀ := K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  let e₁ := K.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
  apply (ModuleCat.mono_iff_injective e₁.hom).mp inferInstance
  change e₁.hom
      (extendedWindingIntegerCochainElement (X := X) k hk) =
    e₁.hom (extendedWindingIntegerCochainElement (X := X) g hg +
      extendedWindingIntegerCochainElement (X := X) h hh -
      ((K.extend ComplexShape.embeddingUpNat).d
        (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1))
        (extendedPointLogProductDefectVertexCochainElement (X := X)
          g h k hg hh hk hmul))
  rw [map_sub, map_add]
  rw [show (K.extend ComplexShape.embeddingUpNat).d
      (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1) =
      e₀.hom ≫ K.d 0 1 ≫ e₁.inv by
        exact HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat rfl rfl]
  rw [extendedWindingIntegerCochainElement_transport,
    extendedWindingIntegerCochainElement_transport,
    extendedWindingIntegerCochainElement_transport]
  simp only [ConcreteCategory.comp_apply]
  rw [
    extendedPointLogProductDefectVertexCochainElement_transport]
  change pairWindingIntegerCochainElement (X := X) k hk =
    pairWindingIntegerCochainElement (X := X) g hg +
      pairWindingIntegerCochainElement (X := X) h hh -
    e₁.hom (e₁.inv (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.d 0 1
      (pairPointLogProductDefectVertexCochainElement (X := X) g h k hg hh hk hmul)))
  rw [e₁.inv_hom_id_apply]
  exact pairWindingIntegerCochainElement_mul_eq_add_sub_coboundary
    (X := X) g h k hg hh hk hmul

/-- The explicit degree-one lower cochain whose differential corrects the product transition
between relative winding cocycles. -/
def rawRelativeWindingTransitionPrimitive
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).X
      (ComplexShape.embeddingUpNat.f 0) :=
  (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
    (ComplexShape.embeddingUpNat.f 0)
      (extendedPointLogProductDefectVertexCochainElement (X := X) g h k hg hh hk hmul)

/-- The raw winding cochain is visibly the second summand of the mapping cone. -/
lemma rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement
    (g : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) :
    rawRelativeWindingCochain (X := X) g hg =
      (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
        (ComplexShape.embeddingUpNat.f 1)
        (extendedWindingIntegerCochainElement (X := X) g hg) := by
  change ((extendedWindingIntegerCochainHom (X := X) g hg ≫
    (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
      (ComplexShape.embeddingUpNat.f 1)).hom 1) = _
  dsimp [extendedWindingIntegerCochainHom]
  let e := ((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat (i := 1) rfl
  change ((CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
      (ComplexShape.embeddingUpNat.f 1)).hom
      (e.inv.hom
        ((pairWindingIntegerCochainHom (X := X) g hg).hom 1)) = _
  rw [pairWindingIntegerCochainHom_apply_one]
  congr 1
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  rw [e.inv_hom_id_apply]
  simpa [e] using
    (extendedWindingIntegerCochainElement_transport (X := X) g hg).symm

/-- The cone differential of the displayed branch-jump primitive is the second inclusion of
its ordinary cochain differential. -/
lemma mappingCone_d_rawRelativeWindingTransitionPrimitive
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
        (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
      (rawRelativeWindingTransitionPrimitive (X := X) g h k hg hh hk hmul) =
      (CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
        (ComplexShape.embeddingUpNat.f 1)
        ((HomologicalComplex.extend
          (((chainPairFunctor ℚ).obj X).left.linearDualCochainComplex)
          ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 0)
            (ComplexShape.embeddingUpNat.f 1)
          (extendedPointLogProductDefectVertexCochainElement (X := X)
            g h k hg hh hk hmul)) := by
  change (((CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
      (ComplexShape.embeddingUpNat.f 0) ≫
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
        (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)).hom
      (extendedPointLogProductDefectVertexCochainElement (X := X)
        g h k hg hh hk hmul)) = _
  rw [CochainComplex.mappingCone.inr_f_d]
  rfl

/-- The product transition formula as an equality of literal relative mapping-cone cochains.
In particular, local normal coordinates related by multiplication by a unit give cohomologous
relative winding cocycles with an explicitly displayed primitive. -/
theorem rawRelativeWindingCochain_mul_eq_add_sub_coboundary
    (g h k : C(X.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    rawRelativeWindingCochain (X := X) k hk =
      rawRelativeWindingCochain (X := X) g hg +
        rawRelativeWindingCochain (X := X) h hh -
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ X)).d
        (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
        (rawRelativeWindingTransitionPrimitive (X := X) g h k hg hh hk hmul) := by
  rw [rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement,
    rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement,
    rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement,
    mappingCone_d_rawRelativeWindingTransitionPrimitive]
  have h := congrArg
    ((CochainComplex.mappingCone.inr (relativeCochainRestrictionInt ℚ X)).f
      (ComplexShape.embeddingUpNat.f 1))
    (extendedWindingIntegerCochainElement_mul_eq_add_sub_coboundary
      (X := X) g h k hg hh hk hmul)
  simpa only [map_add, map_sub] using h

variable {P Q : TopPair.{0}}

/-- Pull the literal branch-jump primitive back along a map of pairs. -/
def rawRelativeWindingTransitionPrimitivePullback (f : P ⟶ Q)
    (g h k : C(Q.snd, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).X
      (ComplexShape.embeddingUpNat.f 0) :=
  (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 0)
    (rawRelativeWindingTransitionPrimitive (X := Q) g h k hg hh hk hmul)

/-- The explicit product-transition equation is preserved by pullback to a normal chart. -/
theorem rawRelativeWindingCochainPullback_mul_eq_add_sub_coboundary
    (f : P ⟶ Q) (g h k : C(Q.snd, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) :
    rawRelativeWindingCochainPullback f k hk =
      rawRelativeWindingCochainPullback f g hg +
        rawRelativeWindingCochainPullback f h hh -
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).d
        (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
        (rawRelativeWindingTransitionPrimitivePullback f g h k hg hh hk hmul) := by
  change (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1)
      (rawRelativeWindingCochain (X := Q) k hk) = _
  rw [rawRelativeWindingCochain_mul_eq_add_sub_coboundary g h k hg hh hk hmul]
  simp only [map_add, map_sub]
  have hcomm := ConcreteCategory.congr_hom
    ((relativeCochainConeMap ℚ f).comm (ComplexShape.embeddingUpNat.f 0)
      (ComplexShape.embeddingUpNat.f 1))
    (rawRelativeWindingTransitionPrimitive (X := Q) g h k hg hh hk hmul)
  have hcomm' :
      (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).d
          (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
        ((relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 0)
          (rawRelativeWindingTransitionPrimitive (X := Q) g h k hg hh hk hmul)) =
      (relativeCochainConeMap ℚ f).f (ComplexShape.embeddingUpNat.f 1)
        ((CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ Q)).d
          (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
          (rawRelativeWindingTransitionPrimitive (X := Q) g h k hg hh hk hmul)) := by
    simpa only [ConcreteCategory.comp_apply] using hcomm
  rw [← hcomm']
  rfl

end ChernWinding
