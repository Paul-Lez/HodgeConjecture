/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalSlicePurity

/-!
# Explicit flattening and normal purity for graphs

The shear `(a,b) ↦ (a,b-F(a))` flattens the graph of an actual continuous map. Combining
this explicit pair isomorphism with tangent contraction gives chain, homology, and
cohomology normal-slice identifications. The class is normalized by the fixed complex
orientation on the normal fiber.

The hypothesis here is genuinely a graph, not arbitrary separate charts on an embedding.
To apply this to an algebraic immersion one still has to prove that its analytic image
locally is such a graph, with compatible complex normal coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (c : ℕ) (F : E → (Fin c → ℂ)) (hF : Continuous F)

/-- The ambient product paired with the complement of the actual graph. -/
abbrev graphComplementPair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (E × (Fin c → ℂ))) {z | z.2 ≠ F z.1}

/-- A graph is flattened by the explicit continuous shear, with explicit inverse. -/
def graphFlattenHomeomorph : (E × (Fin c → ℂ)) ≃ₜ (E × (Fin c → ℂ)) where
  toFun z := (z.1, z.2 - F z.1)
  invFun z := (z.1, z.2 + F z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (hF.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (hF.comp continuous_fst))

omit [NormedSpace ℝ E] in
@[simp] theorem graphFlattenHomeomorph_graph (a : E) :
    graphFlattenHomeomorph E c F hF (a, F a) = (a, 0) := by
  change (a, F a - F a) = _
  simp

/-- The same shear restricts to a homeomorphism on the complements. -/
def graphFlattenComplementHomeomorph :
    {z : E × (Fin c → ℂ) | z.2 ≠ F z.1} ≃ₜ
      {z : E × (Fin c → ℂ) | z.2 ≠ 0} :=
  (graphFlattenHomeomorph E c F hF).subtype fun z => by
    change (z.2 ≠ F z.1) ↔ z.2 - F z.1 ≠ 0
    simp only [sub_ne_zero]

/-- The actual pair isomorphism, not a supplied purity equivalence. -/
def graphFlattenPairIso : graphComplementPair E c F ≅ normalSlicePair E c where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨graphFlattenHomeomorph E c F hF,
      (graphFlattenHomeomorph E c F hF).continuous⟩)
    (TopCat.ofHom ⟨graphFlattenComplementHomeomorph E c F hF,
      (graphFlattenComplementHomeomorph E c F hF).continuous⟩) (by ext z; rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨(graphFlattenHomeomorph E c F hF).symm,
      (graphFlattenHomeomorph E c F hF).symm.continuous⟩)
    (TopCat.ofHom ⟨(graphFlattenComplementHomeomorph E c F hF).symm,
      (graphFlattenComplementHomeomorph E c F hF).symm.continuous⟩) (by ext z; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      exact (graphFlattenComplementHomeomorph E c F hF).left_inv z
    · ext z
      exact (graphFlattenHomeomorph E c F hF).left_inv z
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      exact (graphFlattenComplementHomeomorph E c F hF).right_inv z
    · ext z
      exact (graphFlattenHomeomorph E c F hF).right_inv z

/-- The homology isomorphism constructed from the actual graph shear and normal projection. -/
def graphNormalRelativeHomologyIso (n : ℕ) :
    RelativeHomology ℚ (graphComplementPair E c F) n ≅
      RelativeHomology ℚ (standardComplexPuncturedPair c) n :=
  ((relativeHomologyFunctor ℚ n).mapIso (graphFlattenPairIso E c F hF)) ≪≫
    normalSliceRelativeHomologyIso E c n

/-- The graph-complement pair is concentrated in normal real dimension `2*c`. -/
theorem graphRelativeHomology_isZero_of_ne (hF : Continuous F) (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (RelativeHomology ℚ (graphComplementPair E c F) n) :=
  (standardComplexLocalHomology_isZero_of_ne c n hn).of_iso
    (graphNormalRelativeHomologyIso E c F hF n)

/-- The normal class at tangent coordinate zero, with exact complex normalization. -/
def graphNormalClass : RelativeHomology ℚ (graphComplementPair E c F) (2 * c) :=
  (graphNormalRelativeHomologyIso E c F hF (2 * c)).inv.hom (standardComplexLocalClass c)

@[simp] theorem graphNormalClass_normalization :
    (graphNormalRelativeHomologyIso E c F hF (2 * c)).hom.hom
      (graphNormalClass E c F hF) = standardComplexLocalClass c :=
  ConcreteCategory.congr_hom (graphNormalRelativeHomologyIso E c F hF (2 * c)).inv_hom_id _

/-- The genuine normal fiber over `a` in graph coordinates. -/
def graphNormalFiber (a : E) :
    standardComplexPuncturedPair c ⟶ graphComplementPair E c F :=
  normalSliceSectionAt E c a ≫ (graphFlattenPairIso E c F hF).inv

omit [NormedSpace ℝ E] in
@[simp] theorem graphNormalFiber_apply (a : E) (v : Fin c → ℂ) :
    TopPair.Hom.fst (graphNormalFiber E c F hF a) v = (a, v + F a) := rfl

/-- Moving the graph's normal fiber leaves the exact complex orientation class unchanged. -/
theorem graphNormalFiber_class (a : E) :
    relativeHomologyMap ℚ (2 * c) (graphNormalFiber E c F hF a)
      (standardComplexLocalClass c) = graphNormalClass E c F hF := by
  rw [graphNormalFiber, relativeHomologyMap_comp, LinearMap.comp_apply, normalSliceSectionAt_class]
  rfl

theorem graphRelativeCohomology_isZero_of_ne (hF : Continuous F) (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (RelativeCohomology ℚ (graphComplementPair E c F) n) :=
  relativeCohomology_isZero ℚ _ n (graphRelativeHomology_isZero_of_ne E c F hF n hn)

end AlgebraicTopology.Singular
