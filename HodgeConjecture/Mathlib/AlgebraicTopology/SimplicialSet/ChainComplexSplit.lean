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

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Split monomorphisms of simplicial chains

Simplicial `n`-chains are a coproduct of copies of the coefficient object indexed by the
`n`-simplices, so a map of simplicial sets injective on `n`-simplices induces a *split*
monomorphism on `n`-chains: the summands outside the image go to zero. Being split, unlike being
monic, is preserved by `Module.Dual` over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
variable {X Y : SSet.{w}} (f : X ⟶ Y) (R : C) (n : ℕ)

/-- The map on simplicial `n`-chains sending the summand of a simplex in the image of `f` to the
summand of a chosen preimage, and every other summand to zero. It retracts `chainComplexMap f R`
when `f` is injective on `n`-simplices; see `SSet.isSplitMono_chainComplexMap_f`. -/
def chainComplexMapRetraction :
    (Y.chainComplex R).X n ⟶ (X.chainComplex R).X n :=
  Cofan.IsColimit.desc (Y.isColimitChainComplexXCofan R n) fun y =>
    open Classical in
    if h : ∃ x : X _⦋n⦌, f.app (op ⦋n⦌) x = y then X.ιChainComplex h.choose else 0

@[reassoc]
lemma ιChainComplex_comp_chainComplexMapRetraction (x : X _⦋n⦌)
    (hf : Function.Injective (f.app (op ⦋n⦌))) :
    Y.ιChainComplex (f.app (op ⦋n⦌) x) ≫ chainComplexMapRetraction f R n =
      X.ιChainComplex x := by
  have h : ∃ x' : X _⦋n⦌, f.app (op ⦋n⦌) x' = f.app (op ⦋n⦌) x := ⟨x, rfl⟩
  refine (Cofan.IsColimit.fac (Y.isColimitChainComplexXCofan R n) _
    (f.app (op ⦋n⦌) x)).trans ?_
  rw [dif_pos h, hf h.choose_spec]

/-- A map of simplicial sets that is injective on `n`-simplices induces a split monomorphism on
simplicial `n`-chains. -/
lemma isSplitMono_chainComplexMap_f (hf : Function.Injective (f.app (op ⦋n⦌))) :
    IsSplitMono ((chainComplexMap f R).f n) :=
  ⟨⟨{ retraction := chainComplexMapRetraction f R n
      id := by
        refine chainComplex_hom_ext fun x => ?_
        rw [← Category.assoc, ι_chainComplexMap_f,
          ιChainComplex_comp_chainComplexMapRetraction f R n x hf, Category.comp_id] }⟩⟩

end SSet

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- A monomorphism of topological spaces induces a split monomorphism on singular `n`-chains. -/
lemma isSplitMono_singularChainComplexFunctor_map_f
    {X Y : TopCat.{w}} (g : X ⟶ Y) [Mono g] (R : C) (n : ℕ) :
    IsSplitMono ((((singularChainComplexFunctor C).obj R).map g).f n) :=
  SSet.isSplitMono_chainComplexMap_f (TopCat.toSSet.map g) R n <| by
    have h : Mono ((TopCat.toSSet.map g).app (op ⦋n⦌)) := inferInstance
    rwa [mono_iff_injective] at h

end AlgebraicTopology
