/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.RelativeCochainCone

/-!
# Raw representatives of cochain classes

This small algebraic interface turns a class in the homology of a nonnegative cochain complex
into a displayed closed cochain.  The representative is selected from the canonical quotient
map from cycles to cohomology; the two accompanying lemmas make both its closedness and the
class it represents explicit.

It is useful at the final stage of a local-to-global construction: once local formulas have
produced a class in the literal global singular-cochain complex, this supplies an actual global
cochain in that same complex. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable (K : CochainComplex AddCommGrpCat ℕ) (n : ℕ)

/-- A cycle whose image is a prescribed cohomology class. -/
noncomputable def cochainCycleRepresentative (a : K.homology n) : K.cycles n :=
  Classical.choose ((AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance a)

/-- The selected cycle maps to the class from which it was selected. -/
lemma cochainCycleRepresentative_spec (a : K.homology n) :
    (K.homologyπ n).hom (cochainCycleRepresentative K n a) = a :=
  Classical.choose_spec ((AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance a)

/-- The underlying raw cochain of the selected cycle. -/
noncomputable def cochainRepresentative (a : K.homology n) : K.X n :=
  (K.iCycles n).hom (cochainCycleRepresentative K n a)

/-- The displayed representative is closed. -/
lemma cochainRepresentative_closed (a : K.homology n) :
    (K.d n (n + 1)).hom (cochainRepresentative K n a) = 0 := by
  change (K.d n (n + 1)).hom ((K.iCycles n).hom _) = 0
  rw [← ConcreteCategory.comp_apply, K.iCycles_d]
  rfl

/-- The selected cycle is recovered from the displayed cochain by the cycle inclusion. -/
lemma iCycles_cochainRepresentative (a : K.homology n) :
    (K.iCycles n).hom (cochainCycleRepresentative K n a) =
      cochainRepresentative K n a := rfl

end HomologicalComplex
