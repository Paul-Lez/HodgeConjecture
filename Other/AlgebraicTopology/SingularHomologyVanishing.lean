/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.SingularCohomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Vanishing of singular homology from a bounded chain model

This file records the chain-model reduction used in top-dimensional manifold homology.
If a chain complex is quasi-isomorphic to singular chains and is exact in a degree, singular
homology vanishes in that degree.  In particular it is enough for the corresponding chain group
of the model to be zero.

For a connected noncompact `n`-manifold, the usual proof supplies precisely such a model in
degree `n`: a locally finite triangulation has no compactly supported top cycle (equivalently,
one can use a dimension-controlled good-cover complex).  Mathlib currently has neither a
manifold triangulation theorem nor the dimension-controlled locally finite good-cover comparison.
The statements below isolate that missing standard topological primitive without postulating a
homology group, a fundamental class, or an `∃!` lift as data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

/-- Exactness of any chain model quasi-isomorphic in degree `n` to rational singular chains
implies vanishing of rational singular homology in that degree. -/
public theorem homology_isZero_of_exact_chainModel
    (X : TopCat) (C : ChainComplex (ModuleCat ℚ) ℕ)
    (f : C ⟶ ((singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj X) (n : ℕ) [QuasiIsoAt f n]
    (hC : C.ExactAt n) : IsZero (Homology ℚ X n) :=
  ((exactAt_iff_of_quasiIsoAt f n).mp hC).isZero_homology

/-- A chain model quasi-isomorphic to rational singular chains and having zero chain group in
degree `n` proves vanishing of rational singular homology in degree `n`.  This is the convenient
form for a CW, simplicial, or good-cover model of dimension strictly below `n`. -/
public theorem homology_isZero_of_isZero_chainModel_degree
    (X : TopCat) (C : ChainComplex (ModuleCat ℚ) ℕ)
    (f : C ⟶ ((singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj X) (n : ℕ) [QuasiIsoAt f n]
    (hC : IsZero (C.X n)) : IsZero (Homology ℚ X n) :=
  homology_isZero_of_exact_chainModel X C f n
    (HomologicalComplex.ExactAt.of_isZero hC)

/-- A full quasi-isomorphism from a model with zero degree-`n` chain group gives the same
vanishing conclusion. -/
public theorem homology_isZero_of_bounded_quasiIso_chainModel
    (X : TopCat) (C : ChainComplex (ModuleCat ℚ) ℕ)
    (f : C ⟶ ((singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj X) [QuasiIso f]
    (n : ℕ) (hC : IsZero (C.X n)) : IsZero (Homology ℚ X n) :=
  homology_isZero_of_isZero_chainModel_degree X C f n hC

end AlgebraicTopology.Singular
