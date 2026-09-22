/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.SingularCochainCohomology

/-!
# Singular cohomology classes represented by literal cochains

The repository's `AlgebraicTopology.Singular.Cohomology` is the dual of singular homology.  This
file records the direct route from a raw closed singular cochain to that model: first take its
class in the homology of the singular cochain complex, then apply the universal-coefficient
equivalence.  It makes the representative used to define a class completely visible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (Y : TopCat.{u}) (n : ℕ)

/-- The singular chain complex with coefficients in `R`. -/
abbrev singularChainComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj Y

/-- Regard a cochain as a map from the rank-one coefficient module. -/
def cochainElementHom
    (φ : ((singularChainComplex R Y).linearDualCochainComplex).X n) :
    ModuleCat.of R R ⟶ ((singularChainComplex R Y).linearDualCochainComplex).X n :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R _ φ)

/-- A closed cochain gives a map into the cycle object of the singular cochain complex. -/
def cochainCycle (φ : ((singularChainComplex R Y).linearDualCochainComplex).X n)
    (hφ : ((singularChainComplex R Y).linearDualCochainComplex).d n (n + 1) φ = 0) :
    ModuleCat.of R R ⟶ ((singularChainComplex R Y).linearDualCochainComplex).cycles n :=
  ((singularChainComplex R Y).linearDualCochainComplex).liftCycles
    (cochainElementHom R Y n φ) (n + 1) (by simp) (by
      ext
      change ((singularChainComplex R Y).linearDualCochainComplex).d n (n + 1)
        (LinearMap.toSpanSingleton R _ φ 1) = 0
      simpa using hφ)

/-- The cohomology class of a literal closed singular cochain, in the cochain-complex model. -/
def cochainCohomologyClass (φ : ((singularChainComplex R Y).linearDualCochainComplex).X n)
    (hφ : ((singularChainComplex R Y).linearDualCochainComplex).d n (n + 1) φ = 0) :
    CochainCohomology R Y n :=
  ((cochainCycle R Y n φ hφ ≫
    ((singularChainComplex R Y).linearDualCochainComplex).homologyπ n).hom) 1

/-- The singular cohomology class represented by a literal closed singular cochain. -/
def singularCohomologyClassOfCochain
    (φ : ((singularChainComplex R Y).linearDualCochainComplex).X n)
    (hφ : ((singularChainComplex R Y).linearDualCochainComplex).d n (n + 1) φ = 0) :
    Cohomology R Y n :=
  cochainCohomologyEquiv R Y n (cochainCohomologyClass R Y n φ hφ)

end AlgebraicTopology.Singular
