/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingRationalCochain
public import Other.AlgebraicGeometry.HolomorphicExponentialSequence
public import Other.AlgebraicTopology.SingularCochainSheaf

/-!
# The exponential sequence and rational singular cochains

Evaluation and winding give natural additive maps from holomorphic functions and units to
rational singular cochains. Their compatibility with the normalized exponential is the
cochain-level input to the comparison of the exponential connecting class with winding.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance exponentialSingularTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- The continuous function underlying a holomorphic additive section. -/
def holomorphicSectionFunction (U : Opens (TopCat.of (ComplexPoint X)))
    (f : (holomorphicAdditiveSheaf X d).obj.obj (op U)) : C(U, ℂ) :=
  ⟨(show C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥U; 𝓘(ℂ, ℂ), ℂ⟯ from f),
    (show C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥U; 𝓘(ℂ, ℂ), ℂ⟯ from f).2.continuous⟩

/-- The continuous function underlying an invertible holomorphic section. -/
def holomorphicUnitFunction (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitSheaf X d).obj.obj (op U)) : C(U, ℂ) :=
  ⟨(show Additive (C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥U; 𝓘(ℂ, ℂ), ℂ⟯)ˣ from u).toMul.val,
    (show Additive (C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥U; 𝓘(ℂ, ℂ), ℂ⟯)ˣ from u).toMul.val.2.continuous⟩

theorem holomorphicUnitFunction_ne_zero (U : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitSheaf X d).obj.obj (op U)) (y : U) :
    holomorphicUnitFunction X d U u y ≠ 0 :=
  ((show Additive (C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥U; 𝓘(ℂ, ℂ), ℂ⟯)ˣ from u).toMul.isUnit.map
    (ContMDiffMap.evalRingHom (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) y)).ne_zero

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation followed by the rational projection, as a map of presheaves. -/
def holomorphicToSingularZero :
    (holomorphicAdditiveSheaf X d).obj ⟶
      singularCochainPresheaf ℚ (TopCat.of (ComplexPoint X)) 0 where
  app U := AddCommGrpCat.ofHom
    { toFun f := (ChernWinding.rationalFunctionCochain (holomorphicSectionFunction X d U.unop f)).hom
      map_zero' := by
        have h := ChernWinding.rationalFunctionCochain_zero (Y := TopCat.of U.unop)
        exact congrArg ModuleCat.Hom.hom h
      map_add' f g := by
        have h := ChernWinding.rationalFunctionCochain_add (Y := TopCat.of U.unop)
          (holomorphicSectionFunction X d U.unop f) (holomorphicSectionFunction X d U.unop g)
        exact congrArg ModuleCat.Hom.hom h }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    exact congrArg ModuleCat.Hom.hom
      (ChernWinding.chainComplexMap_comp_rationalFunctionCochain
        (Y := TopCat.of U.unop) (Y' := TopCat.of V.unop)
        ((Opens.toTopCat (TopCat.of (ComplexPoint X))).map i.unop)
        (holomorphicSectionFunction X d U.unop f)).symm

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Winding, as an additive natural transformation into singular one-cochains. -/
def holomorphicUnitToSingularOne :
    (holomorphicUnitSheaf X d).obj ⟶
      singularCochainPresheaf ℚ (TopCat.of (ComplexPoint X)) 1 where
  app U := AddCommGrpCat.ofHom
    { toFun u := (ChernWinding.rationalWindingCochain (holomorphicUnitFunction X d U.unop u)
        (holomorphicUnitFunction_ne_zero X d U.unop u)).hom
      map_zero' := by
        have h := ChernWinding.rationalWindingCochain_one (Y := TopCat.of U.unop)
        exact congrArg ModuleCat.Hom.hom h
      map_add' u v := by
        have h := ChernWinding.rationalWindingCochain_mul (Y := TopCat.of U.unop) (holomorphicUnitFunction X d U.unop u)
          (holomorphicUnitFunction_ne_zero X d U.unop u)
          (holomorphicUnitFunction X d U.unop v) (holomorphicUnitFunction X d U.unop (u + v))
          (holomorphicUnitFunction_ne_zero X d U.unop v)
          (holomorphicUnitFunction_ne_zero X d U.unop (u + v)) (fun _ => rfl)
        exact congrArg ModuleCat.Hom.hom h }
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro u
    exact congrArg ModuleCat.Hom.hom
      (ChernWinding.chainComplexMap_comp_rationalWindingCochain
        (Y := TopCat.of U.unop) (Y' := TopCat.of V.unop)
        (holomorphicUnitFunction X d U.unop u) (holomorphicUnitFunction_ne_zero X d U.unop u)
        ((Opens.toTopCat (TopCat.of (ComplexPoint X))).map i.unop)
        (holomorphicUnitFunction_ne_zero X d V.unop
          ((holomorphicUnitSheaf X d).obj.map i u))).symm

/-- A holomorphic unit maps to a closed singular cochain. -/
theorem holomorphicUnitToSingularOne_comp_coboundary :
    holomorphicUnitToSingularOne X d ≫
      singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) 1 = 0 := by
  ext U u
  exact congrArg ModuleCat.Hom.hom
    (ChernWinding.d_comp_rationalWindingCochain (Y := TopCat.of U.unop) (holomorphicUnitFunction X d U.unop u)
      (holomorphicUnitFunction_ne_zero X d U.unop u))

/-- The winding of `exp(2πif)` is the singular coboundary of the evaluation of `f`. -/
theorem holomorphicExponential_comp_toSingularOne :
    (holomorphicExponential X d).hom ≫ holomorphicUnitToSingularOne X d =
      holomorphicToSingularZero X d ≫
        singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) 0 := by
  ext U f
  exact congrArg ModuleCat.Hom.hom
    (ChernWinding.rationalWindingCochain_eq_d_comp_rationalFunctionCochain (Y := TopCat.of U.unop)
      (holomorphicUnitFunction X d U.unop ((holomorphicExponential X d).hom.app U f))
      (holomorphicUnitFunction_ne_zero X d U.unop ((holomorphicExponential X d).hom.app U f))
      (holomorphicSectionFunction X d U.unop f) (fun _ => rfl))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integer constants retain their usual normalization under the rational cochain map. -/
theorem integerConstantsToHolomorphicPresheaf_comp_toSingularZero :
    integerConstantsToHolomorphicPresheaf X d ≫ holomorphicToSingularZero X d =
      (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).map
        (AddCommGrpCat.ofHom (Int.castAddHom ℚ)) ≫
      constantsToSingularCochainZero ℚ (TopCat.of (ComplexPoint X)) := by
  ext U n
  change ℤ at n
  change (ChernWinding.rationalFunctionCochain (Y := TopCat.of U.unop)
    (fun _ => (n : ℂ))).hom = (n : ℚ) • (openZeroAugmentation ℚ (TopCat.of (ComplexPoint X)) U).hom
  change _ = ((n : ℚ) • openZeroAugmentation ℚ (TopCat.of (ComplexPoint X)) U).hom
  congr 1
  refine SSet.chainComplex_hom_ext fun v => ?_
  rw [ChernWinding.ιChainComplex_comp_rationalFunctionCochain, Linear.comp_smul]
  change _ = (n : ℚ) • (_ ≫ simplicialZeroAugmentation ℚ _)
  rw [ιChainComplex_comp_simplicialZeroAugmentation]
  have hp : ChernWinding.rationalProjection (n : ℂ) = (n : ℚ) := by
    simpa using ChernWinding.rationalProjection_rat (n : ℚ)
  rw [hp]
  ext
  simp [ChernWinding.scalarHomRat, LinearMap.toSpanSingleton]

/-- Evaluation as a morphism into the sheaf of singular zero-cochains. -/
def holomorphicToSingularZeroSheaf :
    holomorphicAdditiveSheaf X d ⟶ singularCochainSheaf ℚ (TopCat.of (ComplexPoint X)) 0 :=
  ⟨holomorphicToSingularZero X d ≫
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (singularCochainPresheaf ℚ (TopCat.of (ComplexPoint X)) 0)⟩

/-- Winding as a morphism into the sheaf of singular one-cochains. -/
def holomorphicUnitToSingularOneSheaf :
    holomorphicUnitSheaf X d ⟶ singularCochainSheaf ℚ (TopCat.of (ComplexPoint X)) 1 :=
  ⟨holomorphicUnitToSingularOne X d ≫
    toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (singularCochainPresheaf ℚ (TopCat.of (ComplexPoint X)) 1)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sheafification preserves the cocycle identity for winding. -/
theorem holomorphicUnitToSingularOneSheaf_comp_coboundary :
    holomorphicUnitToSingularOneSheaf X d ≫
      singularCochainSheafCoboundary ℚ (TopCat.of (ComplexPoint X)) 1 = 0 := by
  apply Sheaf.hom_ext
  change (holomorphicUnitToSingularOne X d ≫ _) ≫
    sheafifyMap (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) 1) = 0
  rw [Category.assoc, ← toSheafify_naturality
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) 1), ← Category.assoc,
    holomorphicUnitToSingularOne_comp_coboundary, Limits.zero_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exponential and singular differential commute after sheafification. -/
theorem holomorphicExponential_comp_toSingularOneSheaf :
    holomorphicExponential X d ≫ holomorphicUnitToSingularOneSheaf X d =
      holomorphicToSingularZeroSheaf X d ≫
        singularCochainSheafCoboundary ℚ (TopCat.of (ComplexPoint X)) 0 := by
  apply Sheaf.hom_ext
  change (holomorphicExponential X d).hom ≫ (holomorphicUnitToSingularOne X d ≫ _) =
    (holomorphicToSingularZero X d ≫ _) ≫
      sheafifyMap (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) 0)
  rw [Category.assoc, ← toSheafify_naturality
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (singularCochainCoboundary ℚ (TopCat.of (ComplexPoint X)) 0),
    ← Category.assoc, ← Category.assoc,
    holomorphicExponential_comp_toSingularOne]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison extends the canonical inclusion of the integer constants. -/
theorem integerConstantsToHolomorphicSheaf_comp_toSingularZeroSheaf :
    integerConstantsToHolomorphicSheaf X d ≫ holomorphicToSingularZeroSheaf X d =
      integerToFieldConstantSheaf ℚ X 1 ≫
        constantsToSingularCochainZeroSheaf ℚ (TopCat.of (ComplexPoint X)) := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let c := (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).map
    (AddCommGrpCat.ofHom (Int.castAddHom ℚ))
  have hi : integerToFieldConstantSheaf ℚ X 1 = (presheafToSheaf J AddCommGrpCat).map c := by
    change (presheafToSheaf J AddCommGrpCat).map
      ((Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).map
        (AddCommGrpCat.ofHom (integerMultipleAddHom ℚ 1))) = _
    congr 2
    ext
    simp [integerMultipleAddHom]
  rw [hi]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (singularCochainSheaf ℚ (TopCat.of (ComplexPoint X)) 0).property
  change toSheafify J _ ≫ (integerConstantsToHolomorphicSheaf X d).hom ≫
      (holomorphicToSingularZero X d ≫ toSheafify J _) =
    toSheafify J _ ≫ sheafifyMap J c ≫
      sheafifyMap J (constantsToSingularCochainZero ℚ (TopCat.of (ComplexPoint X)))
  rw [← Category.assoc, toSheafify_integerConstantsToHolomorphicSheaf,
    ← Category.assoc, integerConstantsToHolomorphicPresheaf_comp_toSingularZero,
    ← toSheafify_naturality_assoc J c, ← toSheafify_naturality]
  rfl

end AlgebraicGeometry.ComplexPoint
