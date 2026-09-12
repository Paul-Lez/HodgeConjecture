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

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalkwise exactness from local primitives

A short complex of presheaves of abelian groups is exact on the stalk at a point as soon as every
section killed by the second map admits, after shrinking the neighborhood, a preimage under the
first map. This is the presheaf-level input used to check exactness of sheafified complexes such
as the singular-cochain and holomorphic de Rham complexes.

This belongs in `Mathlib/Topology/Sheaves/Stalks.lean`; this file can be deleted once it is
there.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace TopCat.Presheaf

/-- A neighborhood-wise lifting of every local kernel section gives exactness after passing to
the stalk. The lift may be taken after shrinking the original neighborhood. -/
lemma stalkExact_of_locallyPrimitive {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{u} X))
    (hlocal : ∀ (x : X) (U : Opens X) (_hx : x ∈ U)
      (s : S.X₂.obj (.op U)), S.g.app (.op U) s = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U) (t : S.X₁.obj (.op V)),
          S.f.app (.op V) t = S.X₂.map i.op s)
    (x : X) :
    (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq z
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g
      (S.X₂.germ U x hxU s) = 0 at hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
  have hz' : S.X₃.germ U x hxU (S.g.app (.op U) s) =
      S.X₃.germ U x hxU 0 := by
    rw [map_zero]
    exact hz
  obtain ⟨W, hxW, iWU, iWU', hW⟩ :=
    S.X₃.germ_eq x hxU hxU (S.g.app (.op U) s) 0 hz'
  have hWs : S.g.app (.op W) (S.X₂.map iWU.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.naturality, ConcreteCategory.comp_apply]
    simpa using hW
  obtain ⟨V, hxV, iVW, t, ht⟩ :=
    hlocal x W hxW (S.X₂.map iWU.op s) hWs
  refine ⟨S.X₁.germ V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f
      (S.X₁.germ V x hxV t) = S.X₂.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    S.X₂.germ_res_apply iVW x hxV, S.X₂.germ_res_apply iWU x hxW]

end TopCat.Presheaf
