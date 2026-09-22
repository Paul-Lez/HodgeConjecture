/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.WindingRelativeUnitBoundary
public import HodgeConjecture.Lemmas.AlgebraicTopology.RelativeCochainConeNaturality

/-!
# Naturality of the explicit winding class

The raw winding cocycle has a strict pullback formula.  This file records the corresponding
statement after passing to the canonical relative singular cohomology class.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular

namespace ChernWinding

variable {P Q : TopPair.{0}} (f : P ⟶ Q) (g : C(Q.snd, ℂ)) (hg : ∀ y, g y ≠ 0)

lemma rawRelativeWindingCocyclePullback_eq_direct :
    rawRelativeWindingCocyclePullback f g hg =
      rawRelativeWindingCocycle (X := P)
        (g.comp (topMap (TopPair.Hom.snd f)))
        (fun x => hg (TopPair.Hom.snd f x)) := by
  apply (cancel_mono
    ((CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).iCycles
      (ComplexShape.embeddingUpNat.f 1))).mp
  dsimp [rawRelativeWindingCocyclePullback, rawRelativeWindingCocycle]
  rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro z
  have hz : z = z • (1 : ℚ) := by simp
  rw [hz, map_smul, map_smul]
  congr 1
  change rawRelativeWindingCochainPullback f g hg =
    rawRelativeWindingCochain (X := P)
      (g.comp (topMap (TopPair.Hom.snd f)))
      (fun x => hg (TopPair.Hom.snd f x))
  exact rawRelativeWindingCochainPullback_eq_rawRelativeWindingCochain f g hg

theorem relativeCohomologyMap_windingRelativeCochainClass :
    relativeCohomologyMap ℚ 2 f
        (windingRelativeCochainClass (X := Q) g hg) =
      windingRelativeCochainClass (X := P)
        (g.comp (topMap (TopPair.Hom.snd f)))
        (fun x => hg (TopPair.Hom.snd f x)) := by
  let a : (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ Q)).homology ((2 : ℤ) - 1) := by
    convert
      (rawRelativeWindingCocycle (X := Q) g hg ≫
        (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ Q)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)).hom 1 using 1 <;> norm_num
  let b : (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ P)).homology ((2 : ℤ) - 1) := by
    convert
      (rawRelativeWindingCocyclePullback f g hg ≫
        (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)).hom 1 using 1 <;> norm_num
  have ha : relativeCochainConeCohomologyEquivCanonical ℚ Q 2 a =
      windingRelativeCochainClass (X := Q) g hg := by
    dsimp [a, windingRelativeCochainClass]
    rfl
  have hb : relativeCochainConeCohomologyEquivCanonical ℚ P 2 b =
      windingRelativeCochainClass (X := P)
        (g.comp (topMap (TopPair.Hom.snd f)))
        (fun x => hg (TopPair.Hom.snd f x)) := by
    dsimp [b, windingRelativeCochainClass]
    rw [← rawRelativeWindingCocyclePullback_eq_direct f g hg]
    rfl
  have hnat := relativeCochainConeCohomologyEquivCanonical_naturality ℚ f 2 a
  have hraw :
      rawRelativeWindingCocycle (X := Q) g hg ≫
          (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ Q)).homologyπ
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.homologyMap (relativeCochainConeMap ℚ f)
            (ComplexShape.embeddingUpNat.f 1) =
        rawRelativeWindingCocyclePullback f g hg ≫
          (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P)).homologyπ
            (ComplexShape.embeddingUpNat.f 1) := by
    rw [HomologicalComplex.homologyπ_naturality (relativeCochainConeMap ℚ f)
        (ComplexShape.embeddingUpNat.f 1),
      ← Category.assoc, rawRelativeWindingCocyclePullback_eq_cyclesMap]
  calc
    _ = relativeCohomologyMap ℚ 2 f
        (relativeCochainConeCohomologyEquivCanonical ℚ Q 2 a) :=
      congrArg (relativeCohomologyMap ℚ 2 f) ha.symm
    _ = relativeCochainConeCohomologyEquivCanonical ℚ P 2
        ((HomologicalComplex.homologyMap (relativeCochainConeMap ℚ f)
          ((2 : ℤ) - 1)).hom a) := hnat.symm
    _ = relativeCochainConeCohomologyEquivCanonical ℚ P 2 b := by
      congr 1
      change (HomologicalComplex.homologyMap (relativeCochainConeMap ℚ f)
          ((2 : ℤ) - 1)).hom a = b
      dsimp [a, b]
      norm_num
      exact ConcreteCategory.congr_hom hraw 1
    _ = _ := hb

end ChernWinding
