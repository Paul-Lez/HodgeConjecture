/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-!
# Normal-slice reduction for a product support

Contracting the tangent coordinate gives a chain homotopy equivalence from
`(E × ℂ^c, E × (ℂ^c \ {0}))` to the normal point-complement pair, so the homology and
cohomology identifications come from the projection and the zero section. The distinguished
relative class is the image of the normalized `standardComplexLocalClass`. This is the
product-model computation for smooth-support purity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)

/-- The complement of the zero normal slice in a product. -/
abbrev normalSlicePair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (E × (Fin c → ℂ))) {z | z.2 ≠ 0}

/-- Projection to the actual normal point-complement pair. -/
def normalSliceProjection : normalSlicePair E c ⟶ standardComplexPuncturedPair c :=
  TopPair.ofHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
    (TopCat.ofHom ⟨fun z => ⟨z.1.2, z.2⟩,
      by fun_prop⟩) (by ext z; rfl)

/-- The zero tangent section preserves the punctured normal coordinate. -/
def normalSliceSection : standardComplexPuncturedPair c ⟶ normalSlicePair E c :=
  TopPair.ofHom (TopCat.ofHom ⟨fun z => (0, z), continuous_const.prodMk continuous_id⟩)
    (TopCat.ofHom ⟨fun z => ⟨(0, z.1), z.2⟩, by fun_prop⟩) (by ext z; rfl)

omit [NormedSpace ℝ E] in
@[simp] theorem normalSliceSection_projection :
    normalSliceSection E c ≫ normalSliceProjection E c = 𝟙 _ := rfl

/-- The explicit pair homotopy contracts only tangent coordinates. Its normal coordinate
is unchanged, so the complement condition holds throughout, including at the endpoints. -/
def normalSliceContraction :
    TopPair.Homotopy (normalSliceProjection E c ≫ normalSliceSection E c)
      (𝟙 (normalSlicePair E c)) where
  fst :=
    { toFun := fun tz : unitInterval × (E × (Fin c → ℂ)) =>
        ((tz.1 : ℝ) • tz.2.1, tz.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun z => Prod.ext (zero_smul ℝ z.1) rfl
      map_one_left := fun z => Prod.ext (one_smul ℝ z.1) rfl }
  snd :=
    { toFun := fun tz => ⟨((tz.1 : ℝ) • tz.2.1.1, tz.2.1.2), tz.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun z => Subtype.ext (Prod.ext (zero_smul ℝ z.1.1) rfl)
      map_one_left := fun z => Subtype.ext (Prod.ext (one_smul ℝ z.1.1) rfl) }
  w := rfl

/-- Normal projection and zero section are inverse up to the actual relative prism homotopy. -/
def normalSliceRelativeChainHomotopyEquiv :
    HomotopyEquiv ((relativeChainFunctor ℚ).obj (normalSlicePair E c))
      ((relativeChainFunctor ℚ).obj (standardComplexPuncturedPair c)) where
  hom := (relativeChainFunctor ℚ).map (normalSliceProjection E c)
  inv := (relativeChainFunctor ℚ).map (normalSliceSection E c)
  homotopyHomInvId := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      (normalSliceContraction E c).relativeChainHomotopy (R := ℚ)
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp, normalSliceSection_projection,
      CategoryTheory.Functor.map_id])

/-- The induced normal-slice isomorphism in every relative homology degree. -/
def normalSliceRelativeHomologyIso (n : ℕ) :
    RelativeHomology ℚ (normalSlicePair E c) n ≅
      RelativeHomology ℚ (standardComplexPuncturedPair c) n :=
  (normalSliceRelativeChainHomotopyEquiv E c).toHomologyIso n

@[simp] theorem normalSliceRelativeHomologyIso_hom (n : ℕ) :
    (normalSliceRelativeHomologyIso E c n).hom.hom =
      relativeHomologyMap ℚ n (normalSliceProjection E c) := rfl

@[simp] theorem normalSliceRelativeHomologyIso_inv (n : ℕ) :
    (normalSliceRelativeHomologyIso E c n).inv.hom =
      relativeHomologyMap ℚ n (normalSliceSection E c) := rfl

/-- The relative normal class uses the exact complex orientation, transported by the
actual zero tangent section. -/
def normalSliceClass : RelativeHomology ℚ (normalSlicePair E c) (2 * c) :=
  relativeHomologyMap ℚ (2 * c) (normalSliceSection E c) (standardComplexLocalClass c)

@[simp] theorem normalSliceProjection_class :
    relativeHomologyMap ℚ (2 * c) (normalSliceProjection E c) (normalSliceClass E c) =
      standardComplexLocalClass c := by
  exact ConcreteCategory.congr_hom (normalSliceRelativeHomologyIso E c (2 * c)).inv_hom_id _

end AlgebraicTopology.Singular
