/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.FirstQuadrantRowwiseTotalization

/-!
# Totalization of a single horizontal column

This elementary chain isomorphism is coefficient-general.  In particular, it lets the
coefficient-`ℚ` augmented Čech comparison land in the ordinary rational singular chain complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicTopology

variable {C : Type 1} [Category C] [Abelian C] [HasCoproducts C] [AB4 C]

local notation "FirstQuadrantBicomplex" => AlgebraicTopology.FirstQuadrantBicomplex C
local notation "FirstQuadrantChainComplex" => AlgebraicTopology.FirstQuadrantChainComplex C

/-- Put a chain complex in horizontal degree zero of a first-quadrant bicomplex. -/
public noncomputable abbrev firstQuadrantSingleZeroBicomplexGeneric
    (K : FirstQuadrantChainComplex) : FirstQuadrantBicomplex :=
  (ChainComplex.single₀ (ChainComplex C ℕ)).obj K

/-- The degree-zero horizontal column is canonically the original chain complex. -/
public noncomputable def firstQuadrantSingleZeroColumnIsoGeneric
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplexGeneric K).X 0 ≅ K :=
  HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 K

/-- The canonical inclusion of the horizontal zero column into the total complex. -/
public noncomputable def firstQuadrantZeroColumnToTotalGeneric
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplexGeneric K).X 0 ⟶
      (firstQuadrantSingleZeroBicomplexGeneric K).total (ComplexShape.down ℕ) where
  f n := (firstQuadrantSingleZeroBicomplexGeneric K).ιTotal
    (ComplexShape.down ℕ) 0 n n (by simp)
  comm' := by
    intro i j hij
    change _ ≫
      ((firstQuadrantSingleZeroBicomplexGeneric K).D₁
        (ComplexShape.down ℕ) i j +
       (firstQuadrantSingleZeroBicomplexGeneric K).D₂
        (ComplexShape.down ℕ) i j) =
      ((firstQuadrantSingleZeroBicomplexGeneric K).X 0).d i j ≫ _
    rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    have hd₁ : (firstQuadrantSingleZeroBicomplexGeneric K).d₁
        (ComplexShape.down ℕ) 0 i j = 0 := by
      apply HomologicalComplex₂.d₁_eq_zero
      simp
    rw [hd₁, zero_add,
      HomologicalComplex₂.d₂_eq (firstQuadrantSingleZeroBicomplexGeneric K)
        (ComplexShape.down ℕ) 0 hij j (by simp)]
    change (ComplexShape.down ℕ).ε 0 • _ = _
    rw [ComplexShape.ε_zero, one_smul]

/-- Include the unique nonzero column into its total complex. -/
public noncomputable def firstQuadrantSingleZeroToTotalGeneric
    (K : FirstQuadrantChainComplex) :
    K ⟶ (firstQuadrantSingleZeroBicomplexGeneric K).total (ComplexShape.down ℕ) :=
  (firstQuadrantSingleZeroColumnIsoGeneric K).inv ≫
    firstQuadrantZeroColumnToTotalGeneric K

set_option backward.isDefEq.respectTransparency false in
/-- Componentwise projection from a horizontal-zero total complex. -/
public noncomputable def firstQuadrantSingleZeroTotalComponentGeneric
    (K : FirstQuadrantChainComplex) (n p q : ℕ)
    (hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    ((firstQuadrantSingleZeroBicomplexGeneric K).X p).X q ⟶ K.X n := by
  rcases p with _ | p
  · change 0 + q = n at hpq
    simp only [zero_add] at hpq
    subst n
    exact (firstQuadrantSingleZeroColumnIsoGeneric K).hom.f q
  · exact 0

@[simp]
public theorem firstQuadrantSingleZeroTotalComponentGeneric_zero
    (K : FirstQuadrantChainComplex) (q : ℕ) :
    firstQuadrantSingleZeroTotalComponentGeneric K q 0 q (by simp) =
      (firstQuadrantSingleZeroColumnIsoGeneric K).hom.f q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Project the total complex supported in horizontal degree zero back to its unique column. -/
public noncomputable def firstQuadrantTotalToSingleZeroGeneric
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplexGeneric K).total (ComplexShape.down ℕ) ⟶ K where
  f n := (firstQuadrantSingleZeroBicomplexGeneric K).totalDesc
    (firstQuadrantSingleZeroTotalComponentGeneric K n)
  comm' := by
    intro i j hij
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rcases p with _ | p
    · have hqi : q = i := by simpa using hpq
      subst q
      rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp only [firstQuadrantSingleZeroTotalComponentGeneric_zero]
      rw [(firstQuadrantSingleZeroColumnIsoGeneric K).hom.comm i j]
      change ((firstQuadrantSingleZeroBicomplexGeneric K).X 0).d i j ≫
          (firstQuadrantSingleZeroColumnIsoGeneric K).hom.f j =
        (firstQuadrantSingleZeroBicomplexGeneric K).ιTotal
            (ComplexShape.down ℕ) 0 i i (by simp) ≫
            ((firstQuadrantSingleZeroBicomplexGeneric K).D₁
                (ComplexShape.down ℕ) i j +
              (firstQuadrantSingleZeroBicomplexGeneric K).D₂
                (ComplexShape.down ℕ) i j) ≫ _
      rw [← Category.assoc, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.ι_D₂]
      have hd₁ : (firstQuadrantSingleZeroBicomplexGeneric K).d₁
          (ComplexShape.down ℕ) 0 i j = 0 := by
        apply HomologicalComplex₂.d₁_eq_zero
        simp
      rw [hd₁, zero_add,
        HomologicalComplex₂.d₂_eq (firstQuadrantSingleZeroBicomplexGeneric K)
          (ComplexShape.down ℕ) 0 hij j (by simp)]
      simp
    · have hzcol : IsZero
          ((firstQuadrantSingleZeroBicomplexGeneric K).X (p + 1)) :=
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 K (p + 1) (by lia)
      have hz : IsZero
          (((firstQuadrantSingleZeroBicomplexGeneric K).X (p + 1)).X q) :=
        (HomologicalComplex.eval C (ComplexShape.down ℕ) q).map_isZero hzcol
      exact hz.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- Projection after inclusion is the identity of the unique column. -/
public theorem firstQuadrantSingleZeroToTotalGeneric_comp_projection
    (K : FirstQuadrantChainComplex) :
    firstQuadrantSingleZeroToTotalGeneric K ≫
      firstQuadrantTotalToSingleZeroGeneric K = 𝟙 K := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [firstQuadrantSingleZeroToTotalGeneric,
    firstQuadrantTotalToSingleZeroGeneric,
    firstQuadrantZeroColumnToTotalGeneric]
  simp only [HomologicalComplex.comp_f]
  rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
  change (firstQuadrantSingleZeroColumnIsoGeneric K).inv.f n ≫
      (firstQuadrantSingleZeroColumnIsoGeneric K).hom.f n = 𝟙 _
  exact congrArg (fun f => f.f n)
    (firstQuadrantSingleZeroColumnIsoGeneric K).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion after projection is the identity of the total complex. -/
public theorem firstQuadrantTotalToSingleZeroGeneric_comp_inclusion
    (K : FirstQuadrantChainComplex) :
    firstQuadrantTotalToSingleZeroGeneric K ≫
      firstQuadrantSingleZeroToTotalGeneric K = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rcases p with _ | p
  · have hqn : n = q := by simpa using hpq.symm
    cases hqn
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    dsimp only [firstQuadrantTotalToSingleZeroGeneric,
      firstQuadrantSingleZeroToTotalGeneric]
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
    simp [firstQuadrantSingleZeroTotalComponentGeneric,
      firstQuadrantSingleZeroColumnIsoGeneric]
    rfl
  · have hzcol : IsZero
        ((firstQuadrantSingleZeroBicomplexGeneric K).X (p + 1)) :=
      HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 K (p + 1) (by lia)
    have hz : IsZero
        (((firstQuadrantSingleZeroBicomplexGeneric K).X (p + 1)).X q) :=
      (HomologicalComplex.eval C (ComplexShape.down ℕ) q).map_isZero hzcol
    exact hz.eq_of_src _ _

/-- The total of a first-quadrant bicomplex concentrated in horizontal degree zero is
canonically isomorphic to its sole column. -/
public noncomputable def firstQuadrantSingleZeroTotalIsoGeneric
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplexGeneric K).total (ComplexShape.down ℕ) ≅ K where
  hom := firstQuadrantTotalToSingleZeroGeneric K
  inv := firstQuadrantSingleZeroToTotalGeneric K
  hom_inv_id := firstQuadrantTotalToSingleZeroGeneric_comp_inclusion K
  inv_hom_id := firstQuadrantSingleZeroToTotalGeneric_comp_projection K

end AlgebraicTopology
