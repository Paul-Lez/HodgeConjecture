/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache License 2.0 as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.ThreeOpenCechTransition
public import Other.AlgebraicTopology.WindingCochainTransition

/-!
# Literal Čech restrictions of winding cochains

This is the bridge between a continuous transition function on an overlap and the
integer-indexed cochain complexes used by the Čech total.  In particular it says that the
restriction of the displayed winding cochain is *definitionally evaluated* by the pullback
function, rather than merely inducing the same class after cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular.CechWinding

open ChernWinding

variable {Y Y' : TopCat.{0}}

/-- Ordinary rational singular cochains, extended by zero to integer degrees for the Čech
mapping-cone convention. -/
abbrev extendedSingularCochains (Y : TopCat.{0}) :
    CochainComplex (ModuleCat ℚ) ℤ :=
  (singularChains Y).linearDualCochainComplex.extend ComplexShape.embeddingUpNat

/-- Pullback of extended singular cochains along a continuous map. -/
def pullback (f : Y' ⟶ Y) :
    extendedSingularCochains Y ⟶ extendedSingularCochains Y' :=
  HomologicalComplex.extendMap
    (HomologicalComplex.linearDualMap
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)))
    ComplexShape.embeddingUpNat

/-- The explicit integer winding cochain, viewed in the integer-indexed convention. -/
def extendedWinding (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    (extendedSingularCochains Y).X (1 : ℤ) :=
  ((singularChains Y).linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) from rfl)).inv
      (windingIntegerCochain g hg).hom

/-- The explicit branch-jump cochain, viewed in the integer-indexed convention. -/
def extendedProductDefect (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) :
    (extendedSingularCochains Y).X (0 : ℤ) :=
  ((singularChains Y).linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).inv
      (pointLogProductDefectVertexCochain g h k hg hh hk hmul).hom

/-- Evaluation of the extended winding cochain recovers the concrete integer winding cochain. -/
lemma extendedWinding_eval (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    ((singularChains Y).linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) from rfl)).hom
      (extendedWinding g hg) =
      (windingIntegerCochain g hg).hom := by
  simp [extendedWinding]

/-- Evaluation of the extended branch-jump cochain recovers its concrete degree-zero formula. -/
lemma extendedProductDefect_eval (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) :
    ((singularChains Y).linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom
        (extendedProductDefect g h k hg hh hk hmul) =
      (pointLogProductDefectVertexCochain g h k hg hh hk hmul).hom := by
  simp [extendedProductDefect]

/-- A literal extended winding cochain is closed. -/
lemma extendedWinding_closed (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) :
    (extendedSingularCochains Y).d (1 : ℤ) (2 : ℤ) (extendedWinding g hg) = 0 := by
  let K := (singularChains Y).linearDualCochainComplex
  let h₁ : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) := rfl
  let h₂ : ComplexShape.embeddingUpNat.f 2 = (2 : ℤ) := rfl
  let e₁ := K.extendXIso ComplexShape.embeddingUpNat h₁
  let e₂ := K.extendXIso ComplexShape.embeddingUpNat h₂
  apply (ModuleCat.mono_iff_injective e₂.hom).mp inferInstance
  change e₂.hom ((K.extend ComplexShape.embeddingUpNat).d (1 : ℤ) (2 : ℤ)
      (extendedWinding g hg)) = e₂.hom 0
  rw [show (K.extend ComplexShape.embeddingUpNat).d
      (1 : ℤ) (2 : ℤ) =
      e₁.hom ≫ K.d 1 2 ≫ e₂.inv by
        exact HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat h₁ h₂]
  simp only [ConcreteCategory.comp_apply, map_zero]
  rw [e₂.inv_hom_id_apply]
  rw [extendedWinding_eval]
  change ((singularChains Y).d 2 1 ≫ windingIntegerCochain g hg).hom = 0
  rw [d_comp_windingIntegerCochain]
  rfl

/-- The product law for winding is an equality of extended raw cochains.  Its last term is the
specified degree-zero principal-branch defect, not a cochain chosen from an existential
argument. -/
lemma extendedWinding_mul_eq_add_sub_coboundary
    (g h k : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    extendedWinding k hk = extendedWinding g hg + extendedWinding h hh -
      (extendedSingularCochains Y).d (0 : ℤ) (1 : ℤ)
        (extendedProductDefect g h k hg hh hk hmul) := by
  let K := (singularChains Y).linearDualCochainComplex
  let h₀ : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
  let h₁ : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) := rfl
  let e₀ := K.extendXIso ComplexShape.embeddingUpNat h₀
  let e₁ := K.extendXIso ComplexShape.embeddingUpNat h₁
  apply (ModuleCat.mono_iff_injective e₁.hom).mp inferInstance
  rw [map_sub, map_add, extendedWinding_eval, extendedWinding_eval, extendedWinding_eval]
  rw [show (K.extend ComplexShape.embeddingUpNat).d
      (0 : ℤ) (1 : ℤ) =
      e₀.hom ≫ K.d 0 1 ≫ e₁.inv by
        exact HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat h₀ h₁]
  simp only [ConcreteCategory.comp_apply]
  rw [e₁.inv_hom_id_apply, extendedProductDefect_eval]
  exact windingIntegerCochainElement_mul_eq_add_sub_coboundary g h k hg hh hk hmul

/-- Pullback of an extended winding cochain is the extended winding cochain of the pulled-back
function, as an equality of raw cochains. -/
lemma pullback_extendedWinding (f : Y' ⟶ Y) (g : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hgf : ∀ y, (g.comp (topMap f)) y ≠ 0) :
    (pullback f).f (1 : ℤ) (extendedWinding g hg) =
      extendedWinding (g.comp (topMap f)) hgf := by
  let K := (singularChains Y).linearDualCochainComplex
  let K' := (singularChains Y').linearDualCochainComplex
  let h₁ : ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) := rfl
  let e := K.extendXIso ComplexShape.embeddingUpNat h₁
  let e' := K'.extendXIso ComplexShape.embeddingUpNat h₁
  apply (ModuleCat.mono_iff_injective e'.hom).mp inferInstance
  change e'.hom ((HomologicalComplex.extendMap
    (HomologicalComplex.linearDualMap
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)))
    ComplexShape.embeddingUpNat).f (1 : ℤ)
      (extendedWinding g hg)) = e'.hom (extendedWinding (g.comp (topMap f)) hgf)
  rw [HomologicalComplex.extendMap_f _ _ (show
    ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) by rfl)]
  simp only [ConcreteCategory.comp_apply]
  rw [e'.inv_hom_id_apply]
  rw [extendedWinding_eval, extendedWinding_eval]
  exact congrArg ModuleCat.Hom.hom
    (chainComplexMap_comp_windingIntegerCochain g hg (f := f) hgf)

/-- Equality of nonvanishing functions transports the displayed extended winding cochain
without any choice; the proof witnesses are irrelevant because nonvanishing is a proposition. -/
lemma extendedWinding_congr (g h : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hgh : g = h) : extendedWinding g hg = extendedWinding h hh := by
  subst h
  rfl

/-- Equality of nowhere-zero functions transports the concrete winding functional itself.
This is the unshifted counterpart of `extendedWinding_congr`, useful when inserting the
cochain into a nonnegative Čech--singular total complex. -/
lemma windingIntegerCochain_congr (g h : C(Y, ℂ)) (hg : ∀ y, g y ≠ 0)
    (hh : ∀ y, h y ≠ 0) (hgh : g = h) :
    windingIntegerCochain g hg = windingIntegerCochain h hh := by
  subst h
  rfl

variable {Y₀₁ Y₀₂ Y₁₂ Y₀₁₂ : TopCat.{0}}

/-- The explicit degree-two transition cochain associated to three nonvanishing coordinate
ratios.  It has winding cochains on `01`, `02`, `12` and the *negative* displayed branch defect
on `012`; this is the sign needed for the standard Čech differential. -/
def threeOpenWindingTransitionCochain
    (f₀₁ : Y₀₁₂ ⟶ Y₀₁) (f₀₂ : Y₀₁₂ ⟶ Y₀₂) (f₁₂ : Y₀₁₂ ⟶ Y₁₂)
    (g₀₁ : C(Y₀₁, ℂ)) (g₀₂ : C(Y₀₂, ℂ)) (g₁₂ : C(Y₁₂, ℂ))
    (hg₀₁ : ∀ y, g₀₁ y ≠ 0) (hg₀₂ : ∀ y, g₀₂ y ≠ 0) (hg₁₂ : ∀ y, g₁₂ y ≠ 0)
    (g h k : C(Y₀₁₂, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y) :
    (threeOpenCechTransitionTotal (pullback f₀₁) (pullback f₀₂) (pullback f₁₂)).X 0 :=
  threeOpenCechTransitionCochain (pullback f₀₁) (pullback f₀₂) (pullback f₁₂) 1
    (extendedWinding g₀₁ hg₀₁) (extendedWinding g₀₂ hg₀₂)
    (extendedWinding g₁₂ hg₁₂) (-(extendedProductDefect g h k hg hh hk hmul))

/-- The three coordinate ratios form a closed raw Čech--singular cochain whenever their
restrictions to the triple intersection satisfy `g₀₂ = g₀₁ * g₁₂`.  This is the cochain-level
first-Chern transition calculation, with no cycle-class correspondence invoked. -/
theorem threeOpenWindingTransitionCochain_closed
    (f₀₁ : Y₀₁₂ ⟶ Y₀₁) (f₀₂ : Y₀₁₂ ⟶ Y₀₂) (f₁₂ : Y₀₁₂ ⟶ Y₁₂)
    (g₀₁ : C(Y₀₁, ℂ)) (g₀₂ : C(Y₀₂, ℂ)) (g₁₂ : C(Y₁₂, ℂ))
    (hg₀₁ : ∀ y, g₀₁ y ≠ 0) (hg₀₂ : ∀ y, g₀₂ y ≠ 0) (hg₁₂ : ∀ y, g₁₂ y ≠ 0)
    (g h k : C(Y₀₁₂, ℂ)) (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0)
    (hk : ∀ y, k y ≠ 0) (hmul : ∀ y, k y = g y * h y)
    (h₀₁ : g₀₁.comp (topMap f₀₁) = g)
    (h₀₂ : g₀₂.comp (topMap f₀₂) = k)
    (h₁₂ : g₁₂.comp (topMap f₁₂) = h) :
    (threeOpenCechTransitionTotal (pullback f₀₁) (pullback f₀₂) (pullback f₁₂)).d 0 1
      (threeOpenWindingTransitionCochain f₀₁ f₀₂ f₁₂
        g₀₁ g₀₂ g₁₂ hg₀₁ hg₀₂ hg₁₂ g h k hg hh hk hmul) = 0 := by
  apply threeOpenCechTransitionCochain_closed
    (pullback f₀₁) (pullback f₀₂) (pullback f₁₂) 1
    (extendedWinding g₀₁ hg₀₁) (extendedWinding g₀₂ hg₀₂)
    (extendedWinding g₁₂ hg₁₂) (-(extendedProductDefect g h k hg hh hk hmul))
  · exact extendedWinding_closed g₀₁ hg₀₁
  · exact extendedWinding_closed g₀₂ hg₀₂
  · exact extendedWinding_closed g₁₂ hg₁₂
  · have e₀₁ : (pullback f₀₁).f 1
        (extendedWinding g₀₁ hg₀₁) = extendedWinding g hg := by
      calc
        _ = extendedWinding (g₀₁.comp (topMap f₀₁))
            (fun y => hg₀₁ (topMap f₀₁ y)) :=
          pullback_extendedWinding f₀₁ g₀₁ hg₀₁ _
        _ = extendedWinding g hg := extendedWinding_congr _ _ _ _ h₀₁
    have e₀₂ : (pullback f₀₂).f 1
        (extendedWinding g₀₂ hg₀₂) = extendedWinding k hk := by
      calc
        _ = extendedWinding (g₀₂.comp (topMap f₀₂))
            (fun y => hg₀₂ (topMap f₀₂ y)) :=
          pullback_extendedWinding f₀₂ g₀₂ hg₀₂ _
        _ = extendedWinding k hk := extendedWinding_congr _ _ _ _ h₀₂
    have e₁₂ : (pullback f₁₂).f 1
        (extendedWinding g₁₂ hg₁₂) = extendedWinding h hh := by
      calc
        _ = extendedWinding (g₁₂.comp (topMap f₁₂))
            (fun y => hg₁₂ (topMap f₁₂ y)) :=
          pullback_extendedWinding f₁₂ g₁₂ hg₁₂ _
        _ = extendedWinding h hh := extendedWinding_congr _ _ _ _ h₁₂
    rw [e₀₁, e₀₂, e₁₂, map_neg,
      extendedWinding_mul_eq_add_sub_coboundary g h k hg hh hk hmul]
    abel

end AlgebraicTopology.Singular.CechWinding
