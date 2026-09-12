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

public import Other.AlgebraicGeometry.HodgeFiltration

/-!
# The Hodge decomposition as a hypothesis

The Hodge decomposition theorem says that the rational cohomology `H^n(X; ℚ)` of a smooth
projective complex variety `X` carries a pure Hodge structure of weight `n`, whose Hodge
filtration is the de Rham one. This repository does not prove it. This file states it as the
hypothesis `HasHodgeDecomposition X n`, names the resulting pure Hodge structure
`h.hodgeStructure`, and proves that the Hodge classes of the statement, `Hdg^p(ℚ; X)`, are then
the rational `(p,p)`-classes of that Hodge structure. So the definition of Hodge classes through
the filtration agrees with the classical definition through the Hodge decomposition, whenever the
latter is available.

The hypothesis lives in `ℂ ⊗[ℚ] H^n(X; ℚ)`, with the de Rham filtration pulled back along the
comparison map `fieldToDeRhamComplexification`. It holds exactly when the pulled-back pieces
`F^p ⊓ conj F^q` with `p + q = n` form a direct sum (`hasHodgeDecomposition_iff_isInternal`); the
other two axioms of a pure Hodge structure hold for these pieces without any hypothesis. The
classical statement is the same decomposition of de Rham hypercohomology itself; given the
comparison isomorphism the two are equivalent (`hasHodgeDecomposition_iff_of_bijective`). Neither
is proved here, and neither should be expected without properness: for `X = 𝔾ₘ` and `n = 1` the
pieces `(1,0)` and `(0,1)` coincide. In degree `0` the hypothesis holds for every `X`
(`hasHodgeDecomposition_zero`); in positive degree it forces the complexified comparison map to be
injective (`HasHodgeDecomposition.injective_fieldToDeRhamComplexification`), which the repository
does not prove either.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The Hodge decomposition of `H^n(X; ℚ)`, as a hypothesis: `H^n(X; ℚ)` carries a pure Hodge
structure of weight `n` whose Hodge filtration is the de Rham one, pulled back along the
comparison map. Hodge theory proves this for every smooth projective variety, via the comparison
isomorphism with de Rham hypercohomology; this repository does not. -/
def HasHodgeDecomposition (n : ℕ) : Prop :=
  ∃ H : HodgeStructure (H^n(X; ℚ)) n,
    ∀ p ≤ n, H.filtration p = complexifiedFieldHodgeFiltration ℚ X p n

/-- The Hodge decomposition holds in degree `n` exactly when the pulled-back pieces
`F^p ⊓ conj F^q` with `p + q = n` form a direct sum. -/
theorem hasHodgeDecomposition_iff_isInternal (n : ℕ) :
    HasHodgeDecomposition X n ↔
      DirectSum.IsInternal fun pq : ℕ × ℕ ↦ HodgeStructure.pieceOfFiltration
        (fun p : ℕ ↦ complexifiedFieldHodgeFiltration ℚ X p n) n pq.1 pq.2 :=
  ⟨fun ⟨H, hH⟩ ↦ H.isInternal_pieceOfFiltration hH,
    fun h ↦ ⟨HodgeStructure.ofFiltration _ n h, fun _ hp ↦
      HodgeStructure.filtration_ofFiltration h (complexifiedFieldHodgeFiltration_antitone ℚ X n) hp⟩⟩

/-- In degree `0` the Hodge decomposition holds: `F^0` is everything. -/
theorem hasHodgeDecomposition_zero : HasHodgeDecomposition X 0 := by
  have hF : complexifiedFieldHodgeFiltration ℚ X 0 0 = ⊤ := by
    have : hodgeFiltrationComplexSubmodule X 0 0 = ⊤ := by
      refine Submodule.eq_top_iff'.2 fun α ↦ ?_
      show α ∈ hodgeFiltration X 0 0
      rw [hodgeFiltration_zero_eq_top]
      trivial
    rw [complexifiedFieldHodgeFiltration, this, Submodule.comap_top]
  have key : (fun pq : ℕ × ℕ ↦ HodgeStructure.pieceOfFiltration
      (fun p : ℕ ↦ complexifiedFieldHodgeFiltration ℚ X p ((0 : ℕ) : ℤ)) 0 pq.1 pq.2) =
      fun pq ↦ (HodgeStructure.weightZero (H^((0 : ℕ) : ℤ)(X; ℚ))).piece pq.1 pq.2 := by
    funext pq
    rw [HodgeStructure.piece_weightZero]
    split_ifs with hpq
    · obtain ⟨h₁, h₂⟩ : pq.1 = 0 ∧ pq.2 = 0 := by omega
      rw [HodgeStructure.pieceOfFiltration_of_add_eq hpq, h₁, h₂]
      simp [hF]
    · exact HodgeStructure.pieceOfFiltration_of_add_ne hpq
  rw [hasHodgeDecomposition_iff_isInternal]
  show DirectSum.IsInternal fun pq : ℕ × ℕ ↦ HodgeStructure.pieceOfFiltration
    (fun p : ℕ ↦ complexifiedFieldHodgeFiltration ℚ X p ((0 : ℕ) : ℤ)) 0 pq.1 pq.2
  rw [key]
  exact (HodgeStructure.weightZero _).isInternal

/-- Given the comparison isomorphism, the hypothesis is exactly the classical Hodge decomposition
of de Rham hypercohomology into the pieces `F^p ⊓ conj F^q`, `p + q = n`. -/
theorem hasHodgeDecomposition_iff_of_bijective {n : ℕ}
    (hφ : Function.Bijective (fieldToDeRhamComplexification ℚ X n)) :
    HasHodgeDecomposition X n ↔ DirectSum.IsInternal fun pq : ℕ × ℕ ↦
      if pq.1 + pq.2 = n then hodgePiece X pq.1 pq.2 n else ⊥ := by
  let e := LinearEquiv.ofBijective (fieldToDeRhamComplexification ℚ X n) hφ
  have key : (fun pq : ℕ × ℕ ↦ HodgeStructure.pieceOfFiltration
      (fun p : ℕ ↦ complexifiedFieldHodgeFiltration ℚ X p n) n pq.1 pq.2) =
      (Submodule.orderIsoMapComap e).symm ∘
        fun pq ↦ if pq.1 + pq.2 = n then hodgePiece X pq.1 pq.2 n else ⊥ := by
    funext pq
    simp only [Function.comp, Submodule.orderIsoMapComap_symm_apply]
    split_ifs with hpq
    · rw [HodgeStructure.pieceOfFiltration_of_add_eq hpq, ← complexifiedFieldHodgePiece_eq_inf_comap]
      rfl
    · rw [HodgeStructure.pieceOfFiltration_of_add_ne hpq, Submodule.comap_bot]
      exact e.ker.symm
  rw [hasHodgeDecomposition_iff_isInternal, key,
    DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top,
    DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, iSupIndep_map_orderIso_iff,
    Function.comp_def]
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg (Submodule.orderIsoMapComap e) h
    rw [OrderIso.map_iSup, OrderIso.map_top] at this
    simpa only [OrderIso.apply_symm_apply] using this
  · have := congrArg (Submodule.orderIsoMapComap e).symm h
    rwa [OrderIso.map_iSup, OrderIso.map_top] at this

namespace HasHodgeDecomposition

variable {X} {n : ℕ} (h : HasHodgeDecomposition X n)

/-- The pure Hodge structure of weight `n` on `H^n(X; ℚ)` whose Hodge filtration is the de Rham
one, given the Hodge decomposition. -/
def hodgeStructure : HodgeStructure (H^n(X; ℚ)) n :=
  HodgeStructure.ofFiltration _ n ((hasHodgeDecomposition_iff_isInternal X n).1 h)

lemma hodgeStructure_piece {p q : ℕ} (hpq : p + q = n) :
    h.hodgeStructure.piece p q = complexifiedFieldHodgePiece ℚ X p q n := by
  change HodgeStructure.pieceOfFiltration
    (fun p : ℕ ↦ complexifiedFieldHodgeFiltration ℚ X p n) n p q = _
  rw [HodgeStructure.pieceOfFiltration_of_add_eq hpq, complexifiedFieldHodgePiece_eq_inf_comap]

lemma hodgeStructure_filtration {p : ℕ} (hp : p ≤ n) :
    h.hodgeStructure.filtration p = complexifiedFieldHodgeFiltration ℚ X p n :=
  HodgeStructure.filtration_ofFiltration _ (complexifiedFieldHodgeFiltration_antitone ℚ X n) hp

/-- A pure Hodge structure on `H^n(X; ℚ)` with the de Rham Hodge filtration is the one built from
the Hodge decomposition. -/
theorem eq_hodgeStructure (H : HodgeStructure (H^n(X; ℚ)) n)
    (hH : ∀ p ≤ n, H.filtration p = complexifiedFieldHodgeFiltration ℚ X p n) :
    H = h.hodgeStructure :=
  H.eq_ofFiltration hH

/-- The kernel of the complexified comparison map lies in every Hodge piece: it is killed by the
filtration and by conjugation alike. -/
lemma ker_le_hodgeStructure_piece {p q : ℕ} (hpq : p + q = n) :
    LinearMap.ker (fieldToDeRhamComplexification ℚ X n) ≤ h.hodgeStructure.piece p q := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [h.hodgeStructure_piece hpq, complexifiedFieldHodgePiece_eq_inf_comap]
  refine ⟨?_, ?_⟩
  · show fieldToDeRhamComplexification ℚ X n x ∈ hodgeFiltrationComplexSubmodule X p n
    rw [hx]
    exact zero_mem _
  · show fieldToDeRhamComplexification ℚ X n (HodgeStructure.conjugate _ x) ∈
      hodgeFiltrationComplexSubmodule X q n
    rw [fieldToDeRhamComplexification_conjugate, hx, map_zero]
    exact zero_mem _

include h in
/-- In positive degree the hypothesis forces the complexified comparison map to be injective: its
kernel lies in the two distinct pieces `(n,0)` and `(0,n)`. -/
theorem injective_fieldToDeRhamComplexification (hn : 0 < n) :
    Function.Injective (fieldToDeRhamComplexification ℚ X n) := by
  rw [← LinearMap.ker_eq_bot]
  have hne : ((n, 0) : ℕ × ℕ) ≠ (0, n) := fun h ↦ by
    have := congrArg Prod.fst h
    omega
  refine le_bot_iff.1 ((h.hodgeStructure.isInternal.submodule_iSupIndep.pairwiseDisjoint hne).le_bot.trans'
    (le_inf (h.ker_le_hodgeStructure_piece (by omega)) (h.ker_le_hodgeStructure_piece (by omega))))

end HasHodgeDecomposition

variable {X}

/-- The Hodge classes of the statement are the rational `(p,p)`-classes of any pure Hodge
structure of weight `2p` on `H^{2p}(X; ℚ)` whose `F^p` is the de Rham `F^p`. This is the
classical definition of Hodge classes, once the Hodge decomposition is known; the proof is where
`HodgeStructure.filtration_inf_conjugateFiltration` identifies `F^p ⊓ conj F^p` with the `(p,p)`
piece. -/
theorem hodgeClasses_eq_hodgeClasses_of_filtration_eq (p : ℕ)
    (H : HodgeStructure (H^(2 * p)(X; ℚ)) (2 * p))
    (hH : H.filtration p = complexifiedFieldHodgeFiltration ℚ X p (2 * p)) :
    Hdg^p(ℚ; X) = H.hodgeClasses p := by
  rw [hodgeClasses_eq_comap_ofBase, HodgeStructure.hodgeClasses,
    ← H.filtration_inf_conjugateFiltration (two_mul p).symm, H.conjugateFiltration_eq_comap, hH,
    complexifiedFieldHodgePiece_eq_inf_comap]

/-- Given the Hodge decomposition, the Hodge classes of the statement are the rational
`(p,p)`-classes of the Hodge structure on `H^{2p}(X; ℚ)`. For this Hodge structure the pieces are
`F^p ⊓ conj F^q` by construction, so this is `hodgeClasses_eq_hodgeClasses_of_filtration_eq`
specialised. -/
theorem hodgeClasses_eq_hodgeClasses_hodgeStructure (p : ℕ)
    (h : HasHodgeDecomposition X (2 * p)) :
    Hdg^p(ℚ; X) = h.hodgeStructure.hodgeClasses p :=
  hodgeClasses_eq_hodgeClasses_of_filtration_eq p _ (h.hodgeStructure_filtration (by omega))

variable (X) in
/-- In codimension `0` the identification needs no hypothesis. -/
theorem hodgeClasses_zero_eq_hodgeClasses_hodgeStructure :
    Hdg^0(ℚ; X) = (hasHodgeDecomposition_zero X).hodgeStructure.hodgeClasses 0 :=
  hodgeClasses_eq_hodgeClasses_hodgeStructure 0 (hasHodgeDecomposition_zero X)

end AlgebraicGeometry.ComplexPoint
