/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/
module

public import Other.AlgebraicTopology.RelativeCechConeComparison

/-!
# Raw cochains in a relative Čech cone

The relative Čech comparison is a map of complexes, so its eventual coordinate calculation must
be made before passing to homology.  This file isolates the elementary cone calculation: a closed
ambient cochain `a` together with a complement cochain `b` is closed in the cone exactly when
`δ a = - d b`.  The compatibility equation is an explicit argument; it is never installed as a
typeclass or hidden in a chosen representative.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.RelativeCechConeComparison

variable {K L : CochainComplex (ModuleCat ℚ) ℤ}

/-- The two visible components of a raw cochain in the mapping cone of `δ`. -/
def coneCochain (δ : K ⟶ L) (n : ℤ) (a : K.X n) (b : L.X (n - 1)) :
    (CochainComplex.mappingCone δ).X (n - 1) :=
  (CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) a +
    (CochainComplex.mappingCone.inr δ).f (n - 1) b

/-- A displayed cone cochain whose second component starts in an explicitly equal degree.
This avoids relying on reducibility of arithmetic expressions in the object field of the
mapping cone. -/
def coneCochainOfEq (δ : K ⟶ L) (n m : ℤ) (h : m = n - 1)
    (a : K.X n) (b : L.X m) : (CochainComplex.mappingCone δ).X (n - 1) :=
  coneCochain δ n a ((L.XIsoOfEq h).hom.hom b)

@[simp]
theorem coneCochainOfEq_rfl (δ : K ⟶ L) (n : ℤ)
    (a : K.X n) (b : L.X (n - 1)) :
    coneCochainOfEq δ n (n - 1) rfl a b = coneCochain δ n a b := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A strict map of restriction squares sends the displayed pair of cone components to the
displayed pair of their images.  This is the raw, pre-homology naturality statement used for
concrete evaluations of relative Čech cocycles. -/
theorem mappingConeMap_coneCochain
    {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat ℚ) ℤ}
    (δ₁ : K₁ ⟶ L₁) (δ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : δ₁ ≫ b = a ≫ δ₂) (n : ℤ) (x : K₁.X n) (y : L₁.X (n - 1)) :
    (CochainComplex.mappingCone.map δ₁ δ₂ a b h).f (n - 1)
        (coneCochain δ₁ n x y) =
      coneCochain δ₂ n (a.f n x) (b.f (n - 1) y) := by
  unfold coneCochain
  rw [map_add]
  congr 1
  · change (((CochainComplex.mappingCone.inl δ₁).v n (n - 1) (by omega) ≫
      (CochainComplex.mappingCone.map δ₁ δ₂ a b h).f (n - 1)).hom x) = _
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inl_v_desc_f]
    simp
  · change (((CochainComplex.mappingCone.inr δ₁).f (n - 1) ≫
      (CochainComplex.mappingCone.map δ₁ δ₂ a b h).f (n - 1)).hom y) = _
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl

/-- The mapping-cone naturality calculation with an explicit transport on the lower-degree
component. -/
theorem mappingConeMap_coneCochainOfEq
    {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat ℚ) ℤ}
    (δ₁ : K₁ ⟶ L₁) (δ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (hsq : δ₁ ≫ b = a ≫ δ₂) (n m : ℤ) (h : m = n - 1)
    (x : K₁.X n) (y : L₁.X m) :
    (CochainComplex.mappingCone.map δ₁ δ₂ a b hsq).f (n - 1)
        (coneCochainOfEq δ₁ n m h x y) =
      coneCochainOfEq δ₂ n m h (a.f n x) (b.f m y) := by
  subst m
  simpa only [coneCochainOfEq_rfl] using
    mappingConeMap_coneCochain δ₁ δ₂ a b hsq n x y

/-- `comparison` evaluates on a displayed cone cochain by precomposing its two visible
functionals with the corresponding absolute chain comparisons. -/
theorem comparison_coneCochain
    {C₀ C₁ S₀ S₁ : ChainComplex (ModuleCat ℚ) ℕ}
    (c : C₀ ⟶ C₁) (s : S₀ ⟶ S₁)
    (q₀ : C₀ ⟶ S₀) (q₁ : C₁ ⟶ S₁)
    (h : c ≫ q₁ = q₀ ≫ s) (n : ℤ)
    (x : (S₁.linearDualCochainComplex.extend ComplexShape.embeddingUpNat).X n)
    (y : (S₀.linearDualCochainComplex.extend ComplexShape.embeddingUpNat).X (n - 1)) :
    (comparison c s q₀ q₁ h).f (n - 1)
        (coneCochain (dualMapInt s) n x y) =
      coneCochain (dualMapInt c) n
        ((dualMapInt q₁).f n x) ((dualMapInt q₀).f (n - 1) y) := by
  exact mappingConeMap_coneCochain (dualMapInt s) (dualMapInt c)
    (dualMapInt q₁) (dualMapInt q₀) (dualSquare c s q₀ q₁ h) n x y

/-- `comparison_coneCochain` with an explicit equality transporting the lower-degree
component. -/
theorem comparison_coneCochainOfEq
    {C₀ C₁ S₀ S₁ : ChainComplex (ModuleCat ℚ) ℕ}
    (c : C₀ ⟶ C₁) (s : S₀ ⟶ S₁)
    (q₀ : C₀ ⟶ S₀) (q₁ : C₁ ⟶ S₁)
    (hsq : c ≫ q₁ = q₀ ≫ s) (n m : ℤ) (h : m = n - 1)
    (x : (S₁.linearDualCochainComplex.extend ComplexShape.embeddingUpNat).X n)
    (y : (S₀.linearDualCochainComplex.extend ComplexShape.embeddingUpNat).X m) :
    (comparison c s q₀ q₁ hsq).f (n - 1)
        (coneCochainOfEq (dualMapInt s) n m h x y) =
      coneCochainOfEq (dualMapInt c) n m h
        ((dualMapInt q₁).f n x) ((dualMapInt q₀).f m y) := by
  exact mappingConeMap_coneCochainOfEq (dualMapInt s) (dualMapInt c)
    (dualMapInt q₁) (dualMapInt q₀) (dualSquare c s q₀ q₁ hsq) n m h x y

/-- After transporting the cone degree back along the displayed equality, a cone cochain
with zero ambient component is literally its original lower-degree component. -/
theorem XIsoOfEq_inv_coneCochainOfEq_zero
    (δ : K ⟶ L) (n m : ℤ) (h : m = n - 1) (b : L.X m) :
    ((CochainComplex.mappingCone δ).XIsoOfEq h).inv.hom
        (coneCochainOfEq δ n m h 0 b) =
      (CochainComplex.mappingCone.inr δ).f m b := by
  subst m
  simp [coneCochainOfEq, coneCochain]

/-- The raw cone cochain is closed from the displayed ambient closedness and the displayed
restriction equation `δ a = - d b`. -/
theorem coneCochain_closed (δ : K ⟶ L) (n : ℤ) (a : K.X n) (b : L.X (n - 1))
    (ha : K.d n (n + 1) a = 0)
    (hcompat : δ.f n a = -L.d (n - 1) n b) :
    (CochainComplex.mappingCone δ).d (n - 1) n (coneCochain δ n a b) = 0 := by
  have hinl :
      (CochainComplex.mappingCone δ).d (n - 1) n
          ((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) a) =
        (CochainComplex.mappingCone.inr δ).f n (δ.f n a) -
          (CochainComplex.mappingCone.inl δ).v (n + 1) n (by omega)
            (K.d n (n + 1) a) := by
    change (((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) ≫
      (CochainComplex.mappingCone δ).d (n - 1) n).hom a) = _
    rw [CochainComplex.mappingCone.inl_v_d δ n (n - 1) (n + 1)
      (by omega) (by omega)]
    rfl
  have hinr :
      (CochainComplex.mappingCone δ).d (n - 1) n
          ((CochainComplex.mappingCone.inr δ).f (n - 1) b) =
        (CochainComplex.mappingCone.inr δ).f n (L.d (n - 1) n b) := by
    change (((CochainComplex.mappingCone.inr δ).f (n - 1) ≫
      (CochainComplex.mappingCone δ).d (n - 1) n).hom b) = _
    rw [CochainComplex.mappingCone.inr_f_d]
    rfl
  change (CochainComplex.mappingCone δ).d (n - 1) n
      ((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) a +
        (CochainComplex.mappingCone.inr δ).f (n - 1) b) = 0
  rw [map_add, hinl, hinr, ha, map_zero, sub_zero, hcompat, map_neg]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
public theorem coneCochain_connecting (δ : K ⟶ L) (n : ℤ) (a : K.X n) (b : L.X (n - 1)) :
    ((CochainComplex.mappingCone.triangle δ).mor₃.f (n - 1) ≫
      (CochainComplex.shiftFunctorObjXIso K (1 : ℤ) (n - 1) n (by omega)).hom).hom
        (coneCochain δ n a b) = -a := by
  unfold coneCochain
  rw [map_add]
  change (((CochainComplex.mappingCone.inl δ).v n (n - 1) (by omega) ≫
      (CochainComplex.mappingCone.triangle δ).mor₃.f (n - 1) ≫
      (CochainComplex.shiftFunctorObjXIso K (1 : ℤ) (n - 1) n (by omega)).hom).hom a) +
    (((CochainComplex.mappingCone.inr δ).f (n - 1) ≫
      (CochainComplex.mappingCone.triangle δ).mor₃.f (n - 1) ≫
      (CochainComplex.shiftFunctorObjXIso K (1 : ℤ) (n - 1) n (by omega)).hom).hom b) = -a
  rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f_assoc,
    CochainComplex.mappingCone.inr_f_triangle_mor₃_f_assoc]
  simp


end AlgebraicTopology.RelativeCechConeComparison
