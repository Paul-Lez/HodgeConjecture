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

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The reduced closed subscheme on a closed subset

The reduced induced structure on a closed subset of a scheme, as the subscheme cut out by the
vanishing ideal sheaf of that subset. The reduced closure of a point (`cycleComponent`) is the
special case of the closure of a singleton.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- The reduced closed subscheme on a closed subset. -/
def reducedClosedSubscheme (S : Closeds X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal S).subscheme

/-- The canonical inclusion of the reduced closed subscheme. -/
def reducedClosedSubschemeι (S : Closeds X) : reducedClosedSubscheme S ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal S).subschemeι

instance reducedClosedSubschemeι_isClosedImmersion (S : Closeds X) :
    IsClosedImmersion (reducedClosedSubschemeι S) := by
  change IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal S).subschemeι
  infer_instance

instance reducedClosedSubscheme_isReduced (S : Closeds X) :
    IsReduced (reducedClosedSubscheme S) := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec (.of (Γ(X, U') ⧸ I.ideal U')))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

@[simp] lemma range_reducedClosedSubschemeι (S : Closeds X) :
    Set.range (reducedClosedSubschemeι S) = (S : Set X) :=
  Scheme.IdealSheafData.range_subschemeι _

end AlgebraicGeometry
