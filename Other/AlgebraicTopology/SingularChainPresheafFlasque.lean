/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularChainSheafStalk
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Surjective restriction for relative singular-chain presheaves

Restriction from support in an open `U` to support in a smaller open `V` is the
quotient map

`C_n(X) / C_n(X \ U) ⟶ C_n(X) / C_n(X \ V)`.

This file records categorically that it is an epimorphism.  Thus every fixed
degree of the relative-chain presheaf is flasque.  This is the first input in
the compact-global comparison with locally finite chains.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Restriction of relative chains to a smaller open support is an epimorphism. -/
instance singularChainPresheaf_restriction_epi (n : ℕ)
    {U V : Opens X} (i : V ⟶ U) :
    Epi ((singularChainPresheaf R X n).map i.op) := by
  let hUV : (V : Set X) ⊆ (U : Set X) := i.le
  let a := supportInclusionPairMap X hUV
  let f := ((relativeChainFunctor R).map a).f n
  have hfac :
      (relativeChainProjection R (TopPair.ofSubset (U : Set X)ᶜ)).f n ≫ f =
        (relativeChainProjection R (TopPair.ofSubset (V : Set X)ᶜ)).f n := by
    exact congrArg (fun g ↦ g.f n)
      (relativeChainProjection_supportInclusion R X hUV)
  have hpi : Epi
      ((relativeChainProjection R (TopPair.ofSubset (V : Set X)ᶜ)).f n) :=
    Cofork.IsColimit.epi
      (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
        (R := R) (TopPair.ofSubset (V : Set X)ᶜ) n)
  have hcomp : Epi
      ((relativeChainProjection R (TopPair.ofSubset (U : Set X)ᶜ)).f n ≫ f) :=
    hfac ▸ hpi
  letI := hcomp
  haveI : Epi f := epi_of_epi
    ((relativeChainProjection R (TopPair.ofSubset (U : Set X)ᶜ)).f n) f
  change Epi ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f)
  rw [AddCommGrpCat.epi_iff_surjective]
  exact (ModuleCat.epi_iff_surjective f).mp inferInstance

/-- Every fixed degree of the relative singular-chain presheaf is flasque. -/
instance singularChainPresheaf_isFlasque (n : ℕ) :
    TopCat.Presheaf.IsFlasque (singularChainPresheaf R X n) where
  epi i := singularChainPresheaf_restriction_epi R X n i.unop

end AlgebraicTopology.Singular
