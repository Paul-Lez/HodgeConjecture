/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitProjectiveSpaceChart
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Affine charts of the Segre embedding

The product of two standard affine projective-space charts embeds as a closed subscheme of
the corresponding standard chart of projective space on pairs of coordinates. The map is the
Segre formula `(x, y) ↦ (xₐ yᵦ)`, and its equations are the two-by-two matrix minors.
-/

@[expose] public noncomputable section

open MvPolynomial CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.SegreChart

universe u

variable (R : Type u) [CommRing R]
  {σ τ : Type u} [DecidableEq σ] [DecidableEq τ] (i : σ) (j : τ)

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coordinates on the product of two standard affine charts. -/
abbrev Coordinates := Sum {a : σ // a ≠ i} {b : τ // b ≠ j}

/-- The coordinate ring of the product chart. -/
abbrev Ring := MvPolynomial (Coordinates i j) R

/-- The coordinate `xₐ/xᵢ` on the first factor. -/
def row (a : σ) : Ring R i j :=
  rename Sum.inl (ProjectiveSpaceChart.coordinateValues R i a)

/-- The coordinate `yᵦ/yⱼ` on the second factor. -/
def column (b : τ) : Ring R i j :=
  rename Sum.inr (ProjectiveSpaceChart.coordinateValues R j b)

omit [DecidableEq τ] in
@[simp] theorem row_self : row R i j i = 1 := by simp [row]
omit [DecidableEq σ] in
@[simp] theorem column_self : column R i j j = 1 := by simp [column]
omit [DecidableEq τ] in
@[simp] theorem row_other (a : {a : σ // a ≠ i}) : row R i j a = X (Sum.inl a) := by
  simp [row]
omit [DecidableEq σ] in
@[simp] theorem column_other (b : {b : τ // b ≠ j}) : column R i j b = X (Sum.inr b) := by
  simp [column]

/-- The coordinate homomorphism of the affine Segre chart. -/
def polynomialMap : MvPolynomial {p : σ × τ // p ≠ (i, j)} R →+* Ring R i j :=
  eval₂Hom C (fun p ↦ row R i j p.1.1 * column R i j p.1.2)

@[simp] theorem polynomialMap_C (r : R) : polynomialMap R i j (C r) = C r := by
  simp [polynomialMap]

@[simp] theorem polynomialMap_coordinate (p : σ × τ) :
    polynomialMap R i j (ProjectiveSpaceChart.coordinateValues R (i, j) p) =
      row R i j p.1 * column R i j p.2 := by
  by_cases h : p = (i, j)
  · subst p; simp
  · simp [ProjectiveSpaceChart.coordinateValues, h, polynomialMap]

/-- Choosing the row and column through the pivot gives a section of the coordinate map. -/
def polynomialSection : Ring R i j →+*
    MvPolynomial {p : σ × τ // p ≠ (i, j)} R :=
  eval₂Hom C (Sum.elim
    (fun a ↦ X ⟨(a.1, j), fun h ↦ a.2 (congrArg Prod.fst h)⟩)
    (fun b ↦ X ⟨(i, b.1), fun h ↦ b.2 (congrArg Prod.snd h)⟩))

@[simp] theorem polynomialSection_row (a : σ) :
    polynomialSection R i j (row R i j a) =
      ProjectiveSpaceChart.coordinateValues R (i, j) (a, j) := by
  by_cases h : a = i
  · subst a; simp
  · simp [row, ProjectiveSpaceChart.coordinateValues, h, polynomialSection]

@[simp] theorem polynomialSection_column (b : τ) :
    polynomialSection R i j (column R i j b) =
      ProjectiveSpaceChart.coordinateValues R (i, j) (i, b) := by
  by_cases h : b = j
  · subst b; simp
  · simp [column, ProjectiveSpaceChart.coordinateValues, h, polynomialSection]

@[simp] theorem polynomialMap_comp_section :
    (polynomialMap R i j).comp (polynomialSection R i j) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [polynomialSection]
  · intro p
    cases p with
    | inl a => simp [polynomialSection, polynomialMap]
    | inr b => simp [polynomialSection, polynomialMap]

/-- Each coordinate on the source is the image of a matrix coordinate. -/
theorem polynomialMap_surjective : Function.Surjective (polynomialMap R i j) := by
  intro p
  exact ⟨polynomialSection R i j p, DFunLike.congr_fun (polynomialMap_comp_section R i j) p⟩

/-- A homogeneous two-by-two matrix minor. -/
def minor (a c : σ) (b d : τ) : MvPolynomial (σ × τ) R :=
  X (a, b) * X (c, d) - X (a, d) * X (c, b)

omit [DecidableEq σ] [DecidableEq τ] in
theorem minor_homogeneous (a c : σ) (b d : τ) : (minor R a c b d).IsHomogeneous 2 :=
  (isHomogeneous_X R (a, b) |>.mul (isHomogeneous_X R (c, d))).sub
    (isHomogeneous_X R (a, d) |>.mul (isHomogeneous_X R (c, b)))

/-- The minors involving the distinguished row and column, on the affine chart. -/
def equations : Ideal (MvPolynomial {p : σ × τ // p ≠ (i, j)} R) :=
  Ideal.span (Set.range (fun p : σ × τ ↦
    ProjectiveSpaceChart.dehomogenize R (i, j) (minor R p.1 i p.2 j)))

@[simp] theorem polynomialMap_dehomogenize_minor (a c : σ) (b d : τ) :
    polynomialMap R i j
      (ProjectiveSpaceChart.dehomogenize R (i, j) (minor R a c b d)) = 0 := by
  simp only [minor, map_sub, map_mul, ProjectiveSpaceChart.dehomogenize_X,
    polynomialMap_coordinate]
  ring

/-- The matrix minors are exactly the equations of the affine Segre map. -/
theorem ker_polynomialMap : RingHom.ker (polynomialMap R i j) = equations R i j := by
  apply le_antisymm
  · let q := Ideal.Quotient.mk (equations R i j)
    have h : (q.comp (polynomialSection R i j)).comp (polynomialMap R i j) = q := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [q, polynomialSection]
      · intro p
        have hm := Ideal.subset_span (s := Set.range (fun p : σ × τ ↦
          ProjectiveSpaceChart.dehomogenize R (i, j) (minor R p.1 i p.2 j)))
          (Set.mem_range_self p.1)
        change _ ∈ equations R i j at hm
        rw [← Ideal.Quotient.eq_zero_iff_mem] at hm
        simp only [minor, map_sub, map_mul, ProjectiveSpaceChart.dehomogenize_X,
          ProjectiveSpaceChart.coordinateValues_self, mul_one] at hm
        have hp : ProjectiveSpaceChart.coordinateValues R (i, j) p.1 = X p :=
          ProjectiveSpaceChart.coordinateValues_other R (i, j) p
        rw [hp, sub_eq_zero] at hm
        simpa [polynomialMap, q] using hm.symm
    intro p hp
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q p = 0
    rw [← DFunLike.congr_fun h p]
    simp only [RingHom.comp_apply, RingHom.mem_ker] at hp ⊢
    rw [hp, map_zero, map_zero]
  · rw [equations, Ideal.span_le, Set.range_subset_iff]
    intro p
    exact polynomialMap_dehomogenize_minor R i j p.1 i p.2 j

/-- The quotient by the matrix minors is the coordinate ring of the product chart. -/
def quotientEquiv : (MvPolynomial {p : σ × τ // p ≠ (i, j)} R ⧸ equations R i j) ≃+*
    Ring R i j :=
  (Ideal.quotEquivOfEq (ker_polynomialMap R i j).symm).trans
    (RingHom.quotientKerEquivOfSurjective (polynomialMap_surjective R i j))

/-- The image on the affine chart is exactly the zero locus of the matrix minors. -/
theorem range_SpecMap :
    Set.range (Spec.map (CommRingCat.ofHom (polynomialMap R i j))) =
      PrimeSpectrum.zeroLocus (equations R i j) := by
  rw [show Set.range (Spec.map (CommRingCat.ofHom (polynomialMap R i j))) =
      Set.range (PrimeSpectrum.comap (polynomialMap R i j)) from rfl,
    range_comap_of_surjective _ _ (polynomialMap_surjective R i j), ker_polynomialMap]

variable [Fintype σ] [Fintype τ]

/-- The affine Segre map, with its actual projective-space chart as target. -/
def immersion : Spec (CommRingCat.of (Ring R i j)) ⟶
    (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X (i, j))).toScheme :=
  Spec.map (CommRingCat.ofHom (polynomialMap R i j)) ≫
    (ProjectiveSpaceChart.basicOpenIso R (i, j)).inv

instance immersion_isClosedImmersion : IsClosedImmersion (immersion R i j) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (polynomialMap R i j))) :=
    IsClosedImmersion.spec_of_surjective _ (polynomialMap_surjective R i j)
  unfold immersion
  infer_instance

/-- The Segre chart map into projective space on pairs of homogeneous coordinates. -/
def toProjectiveSpace : Spec (CommRingCat.of (Ring R i j)) ⟶
    Proj (homogeneousSubmodule (σ × τ) R) :=
  immersion R i j ≫ (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X (i, j))).ι

/-- Pulling back any projective coordinate chart gives the product of the corresponding
coordinate basic opens on the two factors. -/
theorem preimage_basicOpen (a : σ) (b : τ) :
    toProjectiveSpace R i j ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X (a, b)) =
        PrimeSpectrum.basicOpen (row R i j a) ⊓ PrimeSpectrum.basicOpen (column R i j b) := by
  change (Spec.map (CommRingCat.ofHom (polynomialMap R i j)) ≫
    ProjectiveSpaceChart.chartMap R (i, j)) ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage,
    ProjectiveSpaceChart.chartMap_preimage_basicOpen R (i, j) 1 _ (isHomogeneous_X R _) zero_lt_one,
    SpecMap_preimage_basicOpen]
  simp only [CommRingCat.hom_ofHom, ProjectiveSpaceChart.dehomogenize_X,
    polynomialMap_coordinate, PrimeSpectrum.basicOpen_mul]

/-- The actual product of the two standard projective-space charts over `Spec R`. -/
def product : Scheme :=
  pullback
    ((Proj.basicOpen (homogeneousSubmodule σ R) (X i)).ι ≫ ProjectiveSpaceChart.toBase R)
    ((Proj.basicOpen (homogeneousSubmodule τ R) (X j)).ι ≫ ProjectiveSpaceChart.toBase R)

/-- The product chart is the affine scheme with the indicated row and column coordinates. -/
def productIso : product R i j ≅ Spec (CommRingCat.of (Ring R i j)) := by
  refine asIso (pullback.map _ _
    (Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial {a : σ // a ≠ i} R)))
    (Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial {b : τ // b ≠ j} R)))
    (ProjectiveSpaceChart.basicOpenIso R i).hom (ProjectiveSpaceChart.basicOpenIso R j).hom
    (𝟙 _) ?_ ?_) ≪≫
      pullbackSpecIso R (MvPolynomial {a : σ // a ≠ i} R)
        (MvPolynomial {b : τ // b ≠ j} R) ≪≫
      Scheme.Spec.mapIso (MvPolynomial.tensorEquivSum R {a : σ // a ≠ i}
        {b : τ // b ≠ j} R).symm.toRingEquiv.toCommRingCatIso.op
  · simpa using (ProjectiveSpaceChart.basicOpenIso_hom_toBase R i).symm
  · simpa using (ProjectiveSpaceChart.basicOpenIso_hom_toBase R j).symm

/-- The actual product of standard projective charts embeds in the matrix-coordinate chart. -/
def productImmersion : product R i j ⟶
    (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X (i, j))).toScheme :=
  (productIso R i j).hom ≫ immersion R i j

instance productImmersion_isClosedImmersion : IsClosedImmersion (productImmersion R i j) := by
  unfold productImmersion
  infer_instance

/-- The local Segre formula is a morphism over the coefficient ring. -/
@[reassoc] theorem toProjectiveSpace_toBase :
    toProjectiveSpace R i j ≫ ProjectiveSpaceChart.toBase R =
      Spec.map (CommRingCat.ofHom (C : R →+* Ring R i j)) := by
  change (Spec.map (CommRingCat.ofHom (polynomialMap R i j)) ≫
    ProjectiveSpaceChart.chartMap R (i, j)) ≫ _ = _
  rw [Category.assoc, ProjectiveSpaceChart.chartMap_toBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact polynomialMap_C R i j r

end AlgebraicGeometry.SegreChart
