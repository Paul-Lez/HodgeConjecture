/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HypercohomologyFlasqueNaturality

/-!
# Naturality of the flasque global-sections comparison for maps of flasque complexes

The bounded-below flasque comparison `hypercohomologyAddEquivGlobalSections` is natural into
K-injective targets. Composing a map of flasque complexes with a K-injective resolution of its
target, and using that global sections of that resolution map is a quasi-isomorphism, gives
naturality for arbitrary maps between bounded-below termwise flasque complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

set_option backward.isDefEq.respectTransparency false in
/-- The flasque global-sections comparison is natural with respect to maps between bounded-below
termwise flasque complexes. -/
theorem hypercohomologyAddEquivGlobalSections_naturality
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (N : ℤ)
    [K.IsStrictlyGE N] [L.IsStrictlyGE N]
    (hK : ∀ q, (K.X q).IsFlasque) (hL : ∀ q, (L.X q).IsFlasque)
    (f : K ⟶ L) (n : ℤ) (a : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSections X L N hL n (hypercohomologyMap X f n a) =
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
        (hypercohomologyAddEquivGlobalSections X K N hK n a) := by
  let Y := TopCat.of (ComplexPoint X)
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  obtain ⟨I, i, hi, hI, hIge⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L N
  let : QuasiIso i := hi
  let : ∀ q : ℤ, Injective (I.X q) := hI
  let : I.IsStrictlyGE N := hIge
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I N
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  let : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i N N hL hIflasque
  have h₁ := hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    X K I N hK (f ≫ i) n a
  have h₂ := hypercohomologyAddEquivGlobalSections_naturality_to_kInjective
    X L I N hL i n (hypercohomologyMap X f n a)
  rw [← hypercohomologyMap_comp_apply, h₁, Functor.map_comp,
    HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply] at h₂
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap ((Γ.mapHomologicalComplex (.up ℤ)).map i) n) :=
    (asIso (HomologicalComplex.homologyMap
      ((Γ.mapHomologicalComplex (.up ℤ)).map i) n)).addCommGroupIsoToAddEquiv.injective
  exact (hinj h₂).symm

end AlgebraicGeometry.ComplexPoint
