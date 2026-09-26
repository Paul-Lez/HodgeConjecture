/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
/-!
# Contracting a cone map with a factorization

A commutative square whose two maps factor through the source of its target arrow
induces a null-homotopic map of cones. This gives explicit contractions of cones
of isomorphisms, also after an additive functor via the canonical cone comparison.
-/

open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
namespace CochainComplex.mappingCone
variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {A B K L : CochainComplex C ℤ} (φ : A ⟶ B) (ψ : K ⟶ L)
  (a : A ⟶ K) (b : B ⟶ L) (h : φ ≫ b = a ≫ ψ)
  (r : B ⟶ K) (ha : φ ≫ r = a) (hb : r ≫ ψ = b)

/-- A factorization of the square gives a null-homotopy through an identity cone. -/
def mapHomotopyZeroOfFactorization : Homotopy (map φ ψ a b h) 0 := by
  let f := map φ (𝟙 K) a r (by simpa using ha)
  let g := map (𝟙 K) ψ (𝟙 K) ψ (by simp)
  have he : map φ ψ a b h = f ≫ g := by
    have hc := map_comp φ (𝟙 K) ψ a r (by simpa using ha) (𝟙 K) ψ (by simp)
    simpa only [Category.comp_id, hb] using hc
  have hh := ((homotopyToZeroOfId K).compLeft f).compRight g
  exact (Homotopy.ofEq he).trans (by simpa using hh)
/-- The cone of an isomorphism is contractible, by factorization through an identity cone. -/
def homotopyToZeroOfIsIso (φ : A ⟶ B) [IsIso φ] :
    Homotopy (𝟙 (mappingCone φ)) 0 := by
  have hh := mapHomotopyZeroOfFactorization φ φ (𝟙 A) (𝟙 B) (by simp)
    (inv φ) (by simp) (by simp)
  simpa only [map_id] using hh

variable {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.Additive]

/-- If an additive functor makes a morphism invertible, its actual image of the
cone is contractible through the canonical cone comparison. -/
def mapHomologicalComplexConeHomotopyZero (φ : A ⟶ B)
    [IsIso ((F.mapHomologicalComplex (.up ℤ)).map φ)] :
    Homotopy (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj (mappingCone φ))) 0 := by
  let e := mapHomologicalComplexIso φ F
  have hh := ((homotopyToZeroOfIsIso ((F.mapHomologicalComplex (.up ℤ)).map φ)).compLeft
    e.hom).compRight e.inv
  simpa only [Category.comp_id, comp_zero, zero_comp, Iso.hom_inv_id] using hh

end CochainComplex.mappingCone
