/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Algebraic duals of chain complexes of modules

This file collects the purely algebraic constructions on the algebraic-dual cochain complex of a
nonnegatively graded chain complex of modules over a commutative ring `R`:

* `CategoryTheory.ShortComplex.linearDual`: the reversed dual of a short complex of modules;
* `HomologicalComplex.linearDualCochainComplex`: the dual cochain complex, together with the
  identification of its degree-`n` short complex with the reversed dual of the degree-`n` short
  complex of the original chain complex;
* `HomologicalComplex.linearDualMap`, `linearDualIso`, `linearDualHomotopy`,
  `linearDualHomotopyEquiv`: contravariant functoriality of the dual cochain complex in chain
  maps, isomorphisms, homotopies and homotopy equivalences;
* exactness of the dual cochain complex is invariant under homotopy equivalence, gives
  primitives for dual cocycles, and holds in positive degrees for the alternating constant
  complex `M ←0- M ←𝟙- M ←0- M ⋯`.

None of this requires field coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]

/-- The reversed algebraic-dual short complex. -/
def linearDual (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap (by
    ext φ x
    change φ (S.g.hom (S.f.hom x)) = 0
    rw [S.moduleCat_zero_apply, map_zero])

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [CommRing R]

/-- The algebraic-dual cochain complex of a nonnegatively graded chain complex of modules. -/
def linearDualCochainComplex (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of R (Module.Dual R (K.X n)))
    (fun n ↦ ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap)
    (fun n ↦ by
      ext φ c
      change φ ((K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom c)) = 0
      rw [show (K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom c) = 0 from
        ConcreteCategory.congr_hom (K.d_comp_d (n + 2) (n + 1) n) c, map_zero])

@[simp]
lemma linearDualCochainComplex_d (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (K.linearDualCochainComplex).d n (n + 1) =
      ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap := by
  simp [linearDualCochainComplex]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`n` short complex of a linear-dual cochain complex is the reversed dual of the
degree-`n` short complex of the original chain complex. -/
def linearDualCochainComplexScIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.sc n ≅ (K.sc n).linearDual := by
  let D := K.linearDualCochainComplex
  have hprev : (ComplexShape.up ℕ).prev n = (ComplexShape.down ℕ).next n := by
    cases n <;> simp
  have hnext : (ComplexShape.up ℕ).next n = (ComplexShape.down ℕ).prev n := by simp
  refine D.isoSc' ((ComplexShape.down ℕ).next n) n
      ((ComplexShape.down ℕ).prev n) hprev hnext ≪≫
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      HomologicalComplex.shortComplexFunctor'_obj_f]
    dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
    cases n with
    | zero =>
        rw [ChainComplex.next_nat_zero]
        change ModuleCat.ofHom (K.d 0 0).hom.dualMap = D.d 0 0
        rw [K.shape 0 0 (by simp), D.shape 0 0 (by simp)]
        ext φ x
        exact map_zero φ
    | succ n =>
        rw [ChainComplex.next_nat_succ]
        exact (linearDualCochainComplex_d K n).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      HomologicalComplex.shortComplexFunctor'_obj_g]
    dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
    rw [ChainComplex.prev]
    exact (linearDualCochainComplex_d K n).symm

variable {K L M : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Algebraic duality sends a map of nonnegative chain complexes contravariantly to a map of
cochain complexes. -/
def linearDualMap (f : K ⟶ L) :
    L.linearDualCochainComplex ⟶ K.linearDualCochainComplex where
  f n := ModuleCat.ofHom (f.f n).hom.dualMap
  comm' i j hij := by
    obtain rfl := hij
    rw [HomologicalComplex.linearDualCochainComplex_d,
      HomologicalComplex.linearDualCochainComplex_d]
    ext φ
    change Module.Dual R (L.X i) at φ
    apply LinearMap.ext
    intro x
    change K.X (i + 1) at x
    change φ ((f.f i).hom ((K.d (i + 1) i).hom x)) =
      φ ((L.d (i + 1) i).hom ((f.f (i + 1)).hom x))
    exact congrArg φ (ConcreteCategory.congr_hom (f.comm (i + 1) i) x).symm

@[simp]
lemma linearDualMap_id (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    linearDualMap (𝟙 K) = 𝟙 K.linearDualCochainComplex :=
  rfl

@[simp]
lemma linearDualMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    linearDualMap (f ≫ g) = linearDualMap g ≫ linearDualMap f :=
  rfl

/-- Algebraic duality sends an isomorphism of chain complexes to an isomorphism of cochain
complexes, reversing its direction. -/
def linearDualIso (e : K ≅ L) :
    L.linearDualCochainComplex ≅ K.linearDualCochainComplex where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  hom_inv_id := by rw [← linearDualMap_comp, e.inv_hom_id, linearDualMap_id]
  inv_hom_id := by rw [← linearDualMap_comp, e.hom_inv_id, linearDualMap_id]

set_option backward.isDefEq.respectTransparency false in
/-- Algebraic duality sends a chain homotopy contravariantly to a cochain homotopy. -/
def linearDualHomotopy {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (linearDualMap f) (linearDualMap g) where
  hom i j := ModuleCat.ofHom (h.hom j i).hom.dualMap
  zero i j hij := by
    change ¬(ComplexShape.down ℕ).Rel i j at hij
    rw [h.zero j i hij]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
          HomologicalComplex.linearDualCochainComplex_d]
        dsimp only [HomologicalComplex.linearDualCochainComplex] at ⊢
        dsimp only [linearDualMap]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change Module.Dual R (L.X 0) at φ
        apply LinearMap.ext
        intro x
        change K.X 0 at x
        have hi := ConcreteCategory.congr_hom (h.comm 0) x
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hi
        simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, ModuleCat.hom_add,
          ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.add_apply,
          LinearMap.zero_apply, LinearMap.dualMap_apply] at ⊢
        simpa [add_assoc] using congrArg φ hi
    | succ n =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
          HomologicalComplex.linearDualCochainComplex_d,
          HomologicalComplex.linearDualCochainComplex_d]
        dsimp only [HomologicalComplex.linearDualCochainComplex] at ⊢
        dsimp only [linearDualMap]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change Module.Dual R (L.X (n + 1)) at φ
        apply LinearMap.ext
        intro x
        change K.X (n + 1) at x
        have hi := ConcreteCategory.congr_hom (h.comm (n + 1)) x
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hi
        simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, ModuleCat.hom_add,
          LinearMap.comp_apply, LinearMap.add_apply, LinearMap.dualMap_apply] at ⊢
        simpa [add_assoc, add_comm, add_left_comm] using congrArg φ hi

/-- Algebraic duality sends a chain-homotopy equivalence contravariantly to a cochain-homotopy
equivalence. -/
def linearDualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv L.linearDualCochainComplex K.linearDualCochainComplex where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (linearDualMap_comp e.inv e.hom).symm).trans <|
      (linearDualHomotopy e.homotopyInvHomId).trans <|
        Homotopy.ofEq (linearDualMap_id L)
  homotopyInvHomId :=
    (Homotopy.ofEq (linearDualMap_comp e.hom e.inv).symm).trans <|
      (linearDualHomotopy e.homotopyHomInvId).trans <|
        Homotopy.ofEq (linearDualMap_id K)

/-- Exactness of the dual cochain complex in a given degree is invariant under chain-homotopy
equivalence of the original chain complexes. -/
lemma linearDualCochainComplex_exactAt_iff_of_homotopyEquiv (e : HomotopyEquiv K L) (n : ℕ) :
    K.linearDualCochainComplex.ExactAt n ↔ L.linearDualCochainComplex.ExactAt n :=
  (exactAt_iff_of_quasiIsoAt (linearDualHomotopyEquiv e).hom n).symm

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the dual cochain complex in degree `n + 1` provides a primitive for every
functional on degree-`(n + 1)` chains that vanishes on boundaries. -/
lemma exists_dual_primitive_of_exactAt (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (hK : K.linearDualCochainComplex.ExactAt (n + 1))
    (φ : Module.Dual R (K.X (n + 1))) (hφ : (K.d (n + 2) (n + 1)).hom.dualMap φ = 0) :
    ∃ ψ : Module.Dual R (K.X n), (K.d (n + 1) n).hom.dualMap ψ = φ := by
  let D := K.linearDualCochainComplex
  have hD : (D.sc' n (n + 1) (n + 2)).Exact :=
    (D.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).mp hK
  rw [ShortComplex.moduleCat_exact_iff] at hD
  obtain ⟨ψ, hψ⟩ := hD φ (by
    change (D.d (n + 1) (n + 2)).hom φ = 0
    rw [linearDualCochainComplex_d]
    exact hφ)
  refine ⟨ψ, ?_⟩
  change (D.d n (n + 1)).hom ψ = φ at hψ
  rwa [linearDualCochainComplex_d] at hψ

set_option backward.isDefEq.respectTransparency false in
/-- The dual of the alternating constant complex `M ←0- M ←𝟙- M ←0- M ⋯` is exact in every
positive degree. -/
lemma alternatingConst_linearDual_exactAt (M : ModuleCat.{u} R) (n : ℕ) :
    (ChainComplex.alternatingConst.obj M).linearDualCochainComplex.ExactAt (n + 1) := by
  let A := ChainComplex.alternatingConst.obj M
  let D := A.linearDualCochainComplex
  rw [D.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
  intro x hx
  change Module.Dual R M at x
  change (D.d (n + 1) (n + 2)).hom x = 0 at hx
  rw [linearDualCochainComplex_d, ModuleCat.hom_ofHom] at hx
  rcases n.even_or_odd with hn | hn
  · -- `A.d (n + 2) (n + 1) = 𝟙`, so `x = 0`.
    have hd : (A.d (n + 2) (n + 1)).hom = LinearMap.id := by
      simp [A, ChainComplex.alternatingConst, HomologicalComplex.alternatingConst, parity_simps,
        hn]
    rw [hd, LinearMap.dualMap_id] at hx
    exact ⟨0, by rw [show x = 0 from hx, map_zero]⟩
  · -- `A.d (n + 1) n = 𝟙`, so `x` is its own primitive.
    have hd : (A.d (n + 1) n).hom = LinearMap.id := by
      simp [A, ChainComplex.alternatingConst, HomologicalComplex.alternatingConst, parity_simps,
        hn]
    refine ⟨x, ?_⟩
    change (D.d n (n + 1)).hom x = x
    rw [linearDualCochainComplex_d, ModuleCat.hom_ofHom, hd, LinearMap.dualMap_id]
    rfl

end HomologicalComplex
