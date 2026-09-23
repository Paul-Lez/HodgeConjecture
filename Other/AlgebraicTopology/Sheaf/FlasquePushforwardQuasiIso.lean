/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueComparison

/-! # Direct images of comparisons between flasque complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false in
/-- Direct image preserves quasi-isomorphisms between bounded-below termwise-flasque complexes.
The comparison is a quasi-isomorphism on every open set of the target. -/
lemma pushforward_map_quasiIso_of_flasque
    {X Y : TopCat.{u}} (g : X ⟶ Y)
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ}
    (f : K ⟶ L) [QuasiIso f]
    (nK nL : ℤ) [K.IsStrictlyGE nK] [L.IsStrictlyGE nL]
    (hK : ∀ n, (K.X n).IsFlasque) (hL : ∀ n, (L.X n).IsFlasque) :
    QuasiIso (((pushforward AddCommGrpCat.{u} g).mapHomologicalComplex (.up ℤ)).map f) := by
  apply quasiIso_of_cofinal_section_quasiIso
  intro y V hyV
  refine ⟨V, le_rfl, hyV, ?_⟩
  change QuasiIso (((supportEvaluation X ((Opens.map g).obj V)).mapHomologicalComplex
    (.up ℤ)).map f)
  exact supportEvaluation_map_quasiIso_of_flasque X _ f nK nL hK hL

end TopCat.Sheaf
