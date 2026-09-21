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

/-- Let `E` be a real normed vector space and `c ∈ ℕ`. This topological pair is `(E × ℂ^c, E × (ℂ^c
\ {0}))`: the subspace consists of points with nonzero normal coordinate. -/
abbrev normalSlicePair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (E × (Fin c → ℂ))) {z | z.2 ≠ 0}

/-- Let `E` be a real normed vector space and `c ∈ ℕ`. This map of pairs `(E × ℂ^c, E × (ℂ^c \ {0}))
→ (ℂ^c,ℂ^c \ {0})` is projection `(u,v) ↦ v`. -/
def normalSliceProjection : normalSlicePair E c ⟶ puncturedPair ℂ c :=
  TopPair.ofHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
    (TopCat.ofHom ⟨fun z => ⟨z.1.2, z.2⟩,
      by fun_prop⟩) (by ext z; rfl)

/-- Let `E` be a real normed vector space and `c ∈ ℕ`. This map of pairs `(ℂ^c,ℂ^c \ {0}) → (E ×
ℂ^c,E × (ℂ^c \ {0}))` sends `v` to `(0,v)`. -/
def normalSliceSection : puncturedPair ℂ c ⟶ normalSlicePair E c :=
  TopPair.ofHom (TopCat.ofHom ⟨fun z => (0, z), continuous_const.prodMk continuous_id⟩)
    (TopCat.ofHom ⟨fun z => ⟨(0, z.1), z.2⟩, by fun_prop⟩) (by ext z; rfl)

omit [NormedSpace ℝ E] in
@[simp] theorem normalSliceSection_projection :
    normalSliceSection E c ≫ normalSliceProjection E c = 𝟙 _ := rfl

/-- Let `E` be a real normed vector space and `c ∈ ℕ`. On the pair `(E × ℂ^c,E × (ℂ^c \ {0}))`, the
formula `(t,(u,v)) ↦ (tu,v)` for `0 ≤ t ≤ 1` defines a homotopy from projection onto the zero
tangent section to the identity. The normal coordinate remains nonzero on the subspace
throughout. -/
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

/-- Let `E` be a real normed vector space and `c ∈ ℕ`. The rational relative singular chain
complexes of `(E × ℂ^c,E × (ℂ^c \ {0}))` and `(ℂ^c,ℂ^c \ {0})` are homotopy equivalent. This
equivalence uses projection `(u,v) ↦ v`, section `v ↦ (0,v)`, and the prism chain homotopy
induced by `(t,(u,v)) ↦ (tu,v)`. -/
def normalSliceRelativeChainHomotopyEquiv :
    HomotopyEquiv ((relativeChainFunctor ℚ).obj (normalSlicePair E c))
      ((relativeChainFunctor ℚ).obj (puncturedPair ℂ c)) where
  hom := (relativeChainFunctor ℚ).map (normalSliceProjection E c)
  inv := (relativeChainFunctor ℚ).map (normalSliceSection E c)
  homotopyHomInvId :=
    (Homotopy.ofEq ((relativeChainFunctor ℚ).map_comp
        (normalSliceProjection E c) (normalSliceSection E c)).symm).trans
      (((normalSliceContraction E c).relativeChainHomotopy (R := ℚ)).trans
        (Homotopy.ofEq ((relativeChainFunctor ℚ).map_id (normalSlicePair E c))))
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp, normalSliceSection_projection,
      CategoryTheory.Functor.map_id])

/-- Let `E` be a real normed vector space and `c ∈ ℕ`. Projection to the normal coordinate induces
this isomorphism `H_n(E × ℂ^c,E × (ℂ^c \ {0});ℚ) ≅ H_n(ℂ^c,ℂ^c \ {0};ℚ)`. Its inverse is induced
by `v ↦ (0,v)`. -/
def normalSliceRelativeHomologyIso (n : ℕ) :
    RelativeHomology ℚ (normalSlicePair E c) n ≅
      RelativeHomology ℚ (puncturedPair ℂ c) n :=
  (normalSliceRelativeChainHomotopyEquiv E c).toHomologyIso n

@[simp] theorem normalSliceRelativeHomologyIso_hom (n : ℕ) :
    (normalSliceRelativeHomologyIso E c n).hom.hom =
      relativeHomologyMap ℚ n (normalSliceProjection E c) := rfl

@[simp] theorem normalSliceRelativeHomologyIso_inv (n : ℕ) :
    (normalSliceRelativeHomologyIso E c n).inv.hom =
      relativeHomologyMap ℚ n (normalSliceSection E c) := rfl

/-- Let `E` be a real normed vector space and `c ∈ ℕ`. This class in `H_{2c}(E × ℂ^c,E × (ℂ^c \
{0});ℚ)` is the image under `v ↦ (0,v)` of the chosen local class in `H_{2c}(ℂ^c,ℂ^c \ {0};ℚ)`.
The latter is obtained from the standard real simplex class using the ordered real and imaginary
coordinates on `ℂ^c`. -/
def normalSliceClass : RelativeHomology ℚ (normalSlicePair E c) (2 * c) :=
  relativeHomologyMap ℚ (2 * c) (normalSliceSection E c) (standardComplexLocalClass ℚ c)

@[simp] theorem normalSliceProjection_class :
    relativeHomologyMap ℚ (2 * c) (normalSliceProjection E c) (normalSliceClass E c) =
      standardComplexLocalClass ℚ c := by
  exact ConcreteCategory.congr_hom (normalSliceRelativeHomologyIso E c (2 * c)).inv_hom_id _

end AlgebraicTopology.Singular
