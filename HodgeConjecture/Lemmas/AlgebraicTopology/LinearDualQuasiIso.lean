/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache License 2.0 as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LinearDualHomologyNaturality

/-!
# Quasi-isomorphisms after dualizing rational chain complexes

For complexes of vector spaces, the universal-coefficient equivalence identifies the map on
dual cohomology with the dual of the map on homology.  Consequently a rational chain
quasi-isomorphism may be used in either direction at the cochain level.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace HomologicalComplex

variable {R : Type u} [Field R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The equivalence on dual cohomology induced by a rational chain quasi-isomorphism. -/
noncomputable def linearDualCohomologyEquivOfQuasiIso (f : K ⟶ L) [QuasiIso f] (n : ℕ) :
    L.linearDualCochainComplex.homology n ≃ₗ[R]
      K.linearDualCochainComplex.homology n :=
  (linearDualHomologyEquiv L n).trans <|
    (isoOfQuasiIsoAt f n).toLinearEquiv.dualMap.trans <|
      (linearDualHomologyEquiv K n).symm

/-- This concrete equivalence is the map induced by the algebraic dual chain map. -/
lemma linearDualCohomologyEquivOfQuasiIso_apply (f : K ⟶ L) [QuasiIso f] (n : ℕ)
    (a : L.linearDualCochainComplex.homology n) :
    linearDualCohomologyEquivOfQuasiIso f n a =
      (homologyMap (linearDualMap f) n).hom a := by
  apply (linearDualHomologyEquiv K n).injective
  apply LinearMap.ext
  intro z
  rw [linearDualHomologyEquiv_naturality f n a z]
  change linearDualHomologyEquiv K n
      (linearDualCohomologyEquivOfQuasiIso f n a) z =
    (homologyMap f n).hom.dualMap (linearDualHomologyEquiv L n a) z
  simp [linearDualCohomologyEquivOfQuasiIso]

/-- The algebraic dual of a quasi-isomorphism of nonnegative rational chain complexes is a
quasi-isomorphism of cochain complexes. -/
theorem linearDualMap_quasiIso (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (linearDualMap f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let e := linearDualCohomologyEquivOfQuasiIso f n
  let e' : L.linearDualCochainComplex.homology n ≅
      K.linearDualCochainComplex.homology n :=
    e.toModuleIso
  have he : homologyMap (linearDualMap f) n = e'.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (linearDualCohomologyEquivOfQuasiIso_apply f n a).symm
  rw [he]
  infer_instance

end HomologicalComplex
