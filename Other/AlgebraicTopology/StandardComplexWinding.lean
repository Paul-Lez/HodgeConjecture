/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.WindingRelativeCocycle
public import Other.AlgebraicTopology.WindingRelativeClass

/-!
# The explicit winding cocycle around the origin in `ℂ`

The normal coordinate on `ℂ \\ {0}` has a literal integer-valued singular `1`-cocycle.  The
mapping-cone cocycle `(0, windingIndex)` is a literal degree-two relative singular cochain of
the origin.  This is the local cochain that will be transported through the affine chart normal
to the hyperplane in projective space.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ChernWinding

open AlgebraicTopology.Singular

/-- The coordinate on the punctured complex line. -/
def standardNormalCoordinate :
    C(puncturedSpace (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ)), ℂ) :=
  ⟨fun z => z.1.1 0,
    continuous_apply 0 |>.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- The standard normal coordinate does not vanish on the punctured complex line. -/
lemma standardNormalCoordinate_ne_zero
    (z : puncturedSpace (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ))) :
    standardNormalCoordinate z ≠ 0 := by
  intro hz
  apply z.2
  rw [Set.mem_singleton_iff]
  funext i
  fin_cases i
  exact hz

/-- The literal integer singular `1`-cocycle of the normal coordinate. -/
def standardNormalWindingCochain :
    (singularChains
      (puncturedSpace (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ)))).X 1 ⟶
      ModuleCat.of ℚ ℚ :=
  windingIntegerCochain standardNormalCoordinate standardNormalCoordinate_ne_zero

/-- The explicit normal winding cochain is closed. -/
lemma standardNormalWindingCochain_closed :
    (singularChains
      (puncturedSpace (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ)))).d 2 1 ≫
      standardNormalWindingCochain = 0 :=
  d_comp_windingIntegerCochain standardNormalCoordinate standardNormalCoordinate_ne_zero

/-- The coordinate on the repository's standard complex normal pair.  This is definitionally
suited to pullback along `chartNormalProjectionPair`. -/
def standardComplexNormalCoordinate : C((standardComplexPuncturedPair 1).snd, ℂ) :=
  ⟨fun z => Subtype.val z 0, (continuous_apply 0).comp continuous_subtype_val⟩

lemma standardComplexNormalCoordinate_ne_zero (z : (standardComplexPuncturedPair 1).snd) :
    standardComplexNormalCoordinate z ≠ 0 := by
  intro hz
  refine z.2 (funext fun j => ?_)
  obtain rfl : j = 0 := Subsingleton.elim _ _
  exact hz

/-- The explicit normal cochain in the standard pair used by flattening charts. -/
def standardComplexRelativeCochain :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ (standardComplexPuncturedPair 1))).X 1 :=
  rawRelativeWindingCochain (X := standardComplexPuncturedPair 1)
    standardComplexNormalCoordinate standardComplexNormalCoordinate_ne_zero

lemma standardComplexRelativeCochain_closed :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ (standardComplexPuncturedPair 1))).d 1 2
      standardComplexRelativeCochain = 0 :=
  rawRelativeWindingCochain_closed (X := standardComplexPuncturedPair 1)
    standardComplexNormalCoordinate standardComplexNormalCoordinate_ne_zero

/-- The literal degree-two relative cone cochain `(0, standardNormalWindingCochain)`. -/
def standardNormalRelativeCochain :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ
        (supportPair (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ))))).X 1 :=
  rawRelativeWindingCochain
    (X := supportPair (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ)))
    standardNormalCoordinate standardNormalCoordinate_ne_zero

/-- The explicit degree-two relative cone cochain is closed. -/
lemma standardNormalRelativeCochain_closed :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ
        (supportPair (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ))))).d 1 2
      standardNormalRelativeCochain = 0 :=
  rawRelativeWindingCochain_closed
    (X := supportPair (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ)))
    standardNormalCoordinate standardNormalCoordinate_ne_zero

/-- The degree-two relative singular class represented by the explicit normal cone cocycle. -/
def standardNormalWindingClass :
    RelativeCohomology ℚ
      (supportPair (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ))) 2 :=
  windingRelativeCochainClass
    (X := supportPair (Set.univ : Set (Fin 1 → ℂ)) ({0} : Set (Fin 1 → ℂ)))
    standardNormalCoordinate standardNormalCoordinate_ne_zero

end ChernWinding
