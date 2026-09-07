/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularStandardSimplexCone

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Iterated barycentric subdivision on singular chains

The canonical *simplicial* barycentric subdivision chain map followed by the maximum-last-vertex
map is chain-homotopic to the identity.  This file records the corresponding statement for every
finite iterate and its homological consequence.

This operator must not be confused with the geometric affine barycentric subdivision of singular
simplices used in the classical small-chain proof.  The maximum-last-vertex map can send a
subdivided flag back over the original simplex (already in degree one), so its iterates do not
make arbitrary singular simplices small for an open cover.  Excision still requires the geometric
operator, its prism, and the adaptive finite-support argument.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory

namespace AlgebraicTopology.Singular

/-- The chain endomorphism obtained by barycentrically subdividing and then applying the
last-vertex map. -/
public noncomputable def barycentricSubdivisionEndomorphism (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ⟶ X.chainComplex (AddCommGrpCat.of ℤ) :=
  barycentricSubdivisionChainMapCanonical X ≫ subdivisionLastVertexChainMap X

/-- The barycentric-subdivision endomorphism is natural in the simplicial set. -/
public theorem barycentricSubdivisionEndomorphism_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.chainComplexMap f (AddCommGrpCat.of ℤ) ≫
        barycentricSubdivisionEndomorphism Y =
      barycentricSubdivisionEndomorphism X ≫
        SSet.chainComplexMap f (AddCommGrpCat.of ℤ) := by
  rw [barycentricSubdivisionEndomorphism, barycentricSubdivisionEndomorphism,
    ← Category.assoc, barycentricSubdivisionChainMapCanonical_naturality,
    Category.assoc, subdivisionLastVertexChainMap_naturality, ← Category.assoc]

/-- One barycentric-subdivision endomorphism is chain-homotopic to the identity. -/
public noncomputable def barycentricSubdivisionEndomorphismHomotopy (X : SSet.{0}) :
    Homotopy (barycentricSubdivisionEndomorphism X)
      (𝟙 (X.chainComplex (AddCommGrpCat.of ℤ))) :=
  barycentricSubdivisionLastVertexHomotopyCanonical X

/-- Categorical iteration of the barycentric-subdivision endomorphism. -/
public noncomputable def barycentricSubdivisionEndomorphismIterate (X : SSet.{0}) :
    ℕ → (X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      X.chainComplex (AddCommGrpCat.of ℤ))
  | 0 => 𝟙 _
  | n + 1 => barycentricSubdivisionEndomorphismIterate X n ≫
      barycentricSubdivisionEndomorphism X

/-- Every finite iterate of the barycentric-subdivision endomorphism is natural. -/
public theorem barycentricSubdivisionEndomorphismIterate_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) : ∀ n : ℕ,
    SSet.chainComplexMap f (AddCommGrpCat.of ℤ) ≫
        barycentricSubdivisionEndomorphismIterate Y n =
      barycentricSubdivisionEndomorphismIterate X n ≫
        SSet.chainComplexMap f (AddCommGrpCat.of ℤ)
  | 0 => by simp [barycentricSubdivisionEndomorphismIterate]
  | n + 1 => by
      rw [barycentricSubdivisionEndomorphismIterate,
        barycentricSubdivisionEndomorphismIterate, ← Category.assoc,
        barycentricSubdivisionEndomorphismIterate_naturality f n,
        Category.assoc, barycentricSubdivisionEndomorphism_naturality, ← Category.assoc]

/-- Every finite iterate of the barycentric-subdivision endomorphism is chain-homotopic to the
identity. -/
public noncomputable def barycentricSubdivisionEndomorphismIterateHomotopy
    (X : SSet.{0}) : ∀ n : ℕ,
    Homotopy (barycentricSubdivisionEndomorphismIterate X n)
      (𝟙 (X.chainComplex (AddCommGrpCat.of ℤ)))
  | 0 => by
      change Homotopy (𝟙 (X.chainComplex (AddCommGrpCat.of ℤ))) (𝟙 _)
      exact Homotopy.refl _
  | n + 1 => by
      simpa [barycentricSubdivisionEndomorphismIterate] using
        (barycentricSubdivisionEndomorphismIterateHomotopy X n).comp
          (barycentricSubdivisionEndomorphismHomotopy X)

/-- Every iterate of barycentric subdivision followed by last vertex induces the identity on
integral homology. -/
public theorem barycentricSubdivisionEndomorphismIterate_homologyMap
    (X : SSet.{0}) (m n : ℕ) :
    HomologicalComplex.homologyMap
        (barycentricSubdivisionEndomorphismIterate X m) n =
      𝟙 ((X.chainComplex (AddCommGrpCat.of ℤ)).homology n) := by
  rw [(barycentricSubdivisionEndomorphismIterateHomotopy X m).homologyMap_eq]
  exact HomologicalComplex.homologyMap_id _ _

end AlgebraicTopology.Singular
