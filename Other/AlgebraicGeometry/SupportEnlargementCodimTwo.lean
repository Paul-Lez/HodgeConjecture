/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ClosedSupportCoheightDimension

/-!
# Enlarging a support by a codimension-two set does not change `H²`

Let `Z ⊆ Z'` be Zariski-closed subsets of the smooth projective variety `X.left` such that every
point of `Z' ∖ Z` has coheight — codimension — at least two. This file proves that the
support-enlargement map `H²_{Z^an}(X^an, ℚ) → H²_{Z'^an}(X^an, ℚ)`
(`enlargeSupportedInjectiveHomology`, `Other/AlgebraicGeometry/DivisorClassComparisonSupport.lean`)
is **bijective**, and records the corollary used downstream: every class supported on `Z'^an`
is the enlargement of a class supported on `Z^an` with the same ordinary class.

The route:

* `TopCat.Sheaf.supportedSectionsEnlarge_bijective_of_vanishing` — the general statement, for
  closed sets `Z₁`, `Z₂` of a topological space and termwise flasque coefficients: enlarging the
  support from `Z₂` to `Z₁ ∪ Z₂` is bijective on `H^n` as soon as `H^{n-1}_{Z₁}`, `H^n_{Z₁}`,
  `H^n_{Z₁ ∩ Z₂}` and `H^{n+1}_{Z₁ ∩ Z₂}` vanish. It is read off from the two splitting short
  exact sequences of `Other/AlgebraicGeometry/SupportUnionSplitting.lean`:
  `0 → Γ_{Z₂} → Γ_{Z₁ ∪ Z₂} → Γ_{Z₁ ∖ Z₂}(X ∖ Z₂) → 0` and
  `0 → Γ_{Z₁ ∩ Z₂} → Γ_{Z₁} → Γ_{Z₁ ∖ Z₂}(X ∖ Z₂) → 0`.
* `exists_closeds_sup_of_codimTwo` — on the Noetherian sober space `X.left`, `Z'` is the union of
  `Z` and a closed set `W` all of whose points have coheight at least two: `W` is the union of
  the irreducible components of `Z'` not contained in `Z`; their generic points lie in `Z' ∖ Z`,
  and coheight is antitone along specialisation.
* `supportedInjectiveHomology_isZero_of_forall_two_le_coheight` — supported cohomology along the
  analytic support of such a `W` vanishes in every degree `< 4`, exactly as in
  `hasCodimensionTwoSupportedVanishing`.

Nothing here is an obligation: every declaration is proved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Enlarging a closed support by a cohomologically invisible piece.** Let `Z₁ = X ∖ U₁` and
`Z₂ = X ∖ U₂` be closed, with union `X ∖ Uu` and intersection `X ∖ Ui`. If the cohomology
supported in `Z₁` vanishes in degrees `n - 1` and `n`, and the cohomology supported in
`Z₁ ∩ Z₂` vanishes in degrees `n` and `n + 1`, then enlarging the support from `Z₂` to
`Z₁ ∪ Z₂` is bijective on `H^n`.

The hypotheses on the four opens are stated as inequalities, so that no transport along
equalities of supports is needed at the point of use. -/
theorem supportedSectionsEnlarge_bijective_of_vanishing
    (U₁ U₂ Uu Ui : Opens X)
    (h₁ : Uu ≤ U₁) (h₂ : Uu ≤ U₂) (hmeet : U₁ ⊓ U₂ ≤ Uu)
    (h₁' : U₁ ≤ Ui) (h₂' : U₂ ≤ Ui) (hcover : Ui ≤ U₁ ⊔ U₂)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (hK : ∀ n, (K.X n).IsFlasque)
    (n : ℤ)
    (hvan₁ : IsZero (supportedSectionsHomology X K U₁ (n - 1)))
    (hvan₁' : IsZero (supportedSectionsHomology X K U₁ n))
    (hvani : IsZero (supportedSectionsHomology X K Ui n))
    (hvani' : IsZero (supportedSectionsHomology X K Ui (n + 1))) :
    Function.Bijective (supportedSectionsEnlarge X K h₂ n) := by
  have hS₁ := supportSplitSectionsShortComplex_shortExact X U₁ U₂ Ui h₁' h₂' hcover K hK
  have hS₂ := supportSplitSectionsShortComplex_shortExact X Uu U₂ U₂ h₂ le_rfl le_sup_right K hK
  set S₁ := supportSplitSectionsShortComplex X U₁ U₂ Ui h₁' h₂' K with hS₁def
  set S₂ := supportSplitSectionsShortComplex X Uu U₂ U₂ h₂ le_rfl K with hS₂def
  -- the support enlargement, on sections over `U₂`, is an isomorphism of complexes
  let ψ : S₁.X₃ ⟶ S₂.X₃ :=
    ((supportEvaluation X U₂).mapHomologicalComplex (.up ℤ)).map
      (((sheafSectionsSupportedOutsideMap X h₁).mapHomologicalComplex (.up ℤ)).app K)
  have hψ : IsIso ψ := by
    have : ∀ j : ℤ, IsIso (ψ.f j) := fun j =>
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (supportedOutsideMap_app_bijective h₁ ((le_of_eq (inf_comm U₂ U₁)).trans hmeet) (K.X j))
    exact HomologicalComplex.Hom.isIso_of_components ψ
  -- the third term of the first sequence vanishes in degrees `n - 1` and `n`
  have hX₃ : ∀ m m' : ℤ, m' = m + 1 → IsZero (supportedSectionsHomology X K U₁ m) →
      IsZero (supportedSectionsHomology X K Ui m') → IsZero (S₁.X₃.homology m) := by
    intro m m' hm hU₁ hUi
    exact (hS₁.homology_exact₃ m m' (by simp [hm])).isZero_of_both_isZero hU₁ hUi
  have hX₃' : ∀ m : ℤ, IsZero (S₁.X₃.homology m) → IsZero (S₂.X₃.homology m) := fun m hz =>
    hz.of_iso (HomologicalComplex.homologyMapIso (asIso ψ) m).symm
  have hz₁ : IsZero (S₂.X₃.homology (n - 1)) :=
    hX₃' _ (hX₃ (n - 1) n (by ring) hvan₁ hvani)
  have hz₂ : IsZero (S₂.X₃.homology n) := hX₃' _ (hX₃ n (n + 1) rfl hvan₁' hvani')
  -- exactness of the second sequence in degree `n`
  have hmono : Mono (HomologicalComplex.homologyMap S₂.f n) :=
    (hS₂.homology_exact₁ (n - 1) n (by simp)).mono_g (hz₁.eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap S₂.f n) :=
    (hS₂.homology_exact₂ n).epi_f (hz₂.eq_of_tgt _ _)
  exact ⟨(AddCommGrpCat.mono_iff_injective _).mp hmono,
    (AddCommGrpCat.epi_iff_surjective _).mp hepi⟩

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance supportEnlargementCodimTwoAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### Monotonicity of the analytic support -/

/-- The analytic support of a Zariski-closed set is monotone. -/
theorem analyticClosedSupport_le_of_le {Z Z' : Closeds X.left} (h : Z ≤ Z') :
    analyticClosedSupport X Z ≤ analyticClosedSupport X Z' :=
  fun _ hz => h hz

/-! ### Splitting off the codimension-two part -/

omit [IsIntegral X.left] [Smooth X.hom] in
/-- **Splitting off the codimension-two part.** If every point of `Z' ∖ Z` has coheight at
least two, then `Z' = Z ∪ W` for a Zariski-closed `W ⊆ Z'` all of whose points have coheight at
least two: `W` is the union of the irreducible components of `Z'` not contained in `Z`. -/
theorem exists_closeds_sup_of_codimTwo (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z')
    (hcod : ∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z) :
    ∃ W : Closeds X.left, W ≤ Z' ∧ Z' ≤ Z ⊔ W ∧ ∀ w ∈ W, (2 : ℕ∞) ≤ coheight w := by
  classical
  obtain ⟨S, hirr, hS⟩ := NoetherianSpace.exists_finset_irreducible Z'
  subst hS
  set f : Closeds X.left → Closeds X.left := fun k => if (k : Set X.left) ⊆ Z then ⊥ else k
    with hf
  have hf_le : ∀ k, f k ≤ k := by
    intro k
    simp only [hf]
    split_ifs
    · exact bot_le
    · exact le_rfl
  have hmem_sup : ∀ (g : Closeds X.left → Closeds X.left) (z : X.left),
      z ∈ S.sup g → ∃ k ∈ S, z ∈ g k := by
    intro g z hz
    have hz' : z ∈ (↑(S.sup g) : Set X.left) := hz
    rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hz'
    obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz'
    exact ⟨k, hk, hzk⟩
  refine ⟨S.sup f, Finset.sup_le fun k hk => (hf_le k).trans (Finset.le_sup (f := id) hk),
    ?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, hzk⟩ := hmem_sup id z hz
    by_cases hkZ : (k : Set X.left) ⊆ Z
    · exact Or.inl (hkZ hzk)
    · refine Or.inr ?_
      have hle : k ≤ S.sup f := by
        have h := Finset.le_sup (f := f) hk
        simpa only [hf, if_neg hkZ] using h
      exact hle hzk
  · intro w hw
    obtain ⟨k, hk, hwk⟩ := hmem_sup f w hw
    by_cases hkZ : (k : Set X.left) ⊆ Z
    · exfalso
      simp only [hf, if_pos hkZ] at hwk
      exact hwk
    · simp only [hf, if_neg hkZ] at hwk
      have hk_irr : IsIrreducible (k : Set X.left) := hirr ⟨k, hk⟩
      have hgen := hk_irr.isGenericPoint_genericPoint k.isClosed
      have hηk : hk_irr.genericPoint ∈ (k : Set X.left) := hgen.mem
      have hηZ' : hk_irr.genericPoint ∈ S.sup id := Finset.le_sup (f := id) hk hηk
      have hηZ : hk_irr.genericPoint ∉ Z := by
        intro hηZ
        apply hkZ
        rw [← hgen.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr hηZ) Z.isClosed
      have hη : (2 : ℕ∞) ≤ coheight hk_irr.genericPoint := hcod _ hηZ' hηZ
      have hwη : w ≤ hk_irr.genericPoint :=
        specializes_iff_mem_closure.mpr (by rw [hgen.def]; exact hwk)
      exact hη.trans (coheight_anti hwη)

/-! ### Vanishing along a codimension-two support -/

/-- Supported cohomology along the analytic support of a Zariski-closed subset of codimension at
least two vanishes in every degree below four (`hasCodimensionTwoSupportedVanishing` is the case
of degree three). -/
theorem supportedInjectiveHomology_isZero_of_forall_two_le_coheight (W : Closeds X.left)
    (hW : ∀ z ∈ W, (2 : ℕ∞) ≤ coheight z) (n : ℤ) (hn : n < 4) :
    IsZero (SupportedInjectiveHomology X (analyticClosedSupport X W) n) := by
  have hstr : ClosedSupportStrataNormalCodimension X W (dim X.left) 2 :=
    closedSupportStrataNormalCodimension_of_forall_le_coheight X W hW
  exact closedSupportSectionCohomology_isZero_of_lt hstr n (by push_cast; omega)

/-! ### The enlargement is bijective -/

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Enlarging the support from `Z^an` to `Z'^an`, where `Z' ⊆ Z ∪ W` for a Zariski-closed
`W ⊆ Z'` of codimension at least two, is bijective on `H^n` for every `n ≤ 2`. -/
theorem enlargeSupportedInjectiveHomology_bijective_of_sup
    {Z W Z' : Closeds X.left} (hZZ' : Z ≤ Z') (hWZ' : W ≤ Z') (hZ' : Z' ≤ Z ⊔ W)
    (hW : ∀ z ∈ W, (2 : ℕ∞) ≤ coheight z) (n : ℤ) (hn : n ≤ 2) :
    Function.Bijective
      (enlargeSupportedInjectiveHomology X (analyticClosedSupport_le_of_le X hZZ') n) := by
  have hWZ : ∀ z ∈ W ⊓ Z, (2 : ℕ∞) ≤ coheight z := fun z hz => hW z hz.1
  have h₁ : (analyticClosedSupport X Z').compl ≤ (analyticClosedSupport X W).compl :=
    fun _ hx hz => hx (hWZ' hz)
  have h₂ : (analyticClosedSupport X Z').compl ≤ (analyticClosedSupport X Z).compl :=
    fun _ hx hz => hx (hZZ' hz)
  have hmeet : (analyticClosedSupport X W).compl ⊓ (analyticClosedSupport X Z).compl ≤
      (analyticClosedSupport X Z').compl := by
    intro z hz hmem
    exact (hZ' hmem).elim (fun h => hz.2 h) (fun h => hz.1 h)
  have h₁' : (analyticClosedSupport X W).compl ≤ (analyticClosedSupport X (W ⊓ Z)).compl :=
    fun _ hx hz => hx hz.1
  have h₂' : (analyticClosedSupport X Z).compl ≤ (analyticClosedSupport X (W ⊓ Z)).compl :=
    fun _ hx hz => hx hz.2
  have hcover : (analyticClosedSupport X (W ⊓ Z)).compl ≤
      (analyticClosedSupport X W).compl ⊔ (analyticClosedSupport X Z).compl := by
    intro z hz
    by_cases hz₁ : z ∈ analyticClosedSupport X W
    · exact Or.inr (fun hz₂ => hz ⟨hz₁, hz₂⟩)
    · exact Or.inl hz₁
  exact TopCat.Sheaf.supportedSectionsEnlarge_bijective_of_vanishing (TopCat.of (ComplexPoint X))
    (analyticClosedSupport X W).compl (analyticClosedSupport X Z).compl
    (analyticClosedSupport X Z').compl (analyticClosedSupport X (W ⊓ Z)).compl
    h₁ h₂ hmeet h₁' h₂' hcover (ambientRationalInjectiveComplex X)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (supportedInjectiveHomology_isZero_of_forall_two_le_coheight X W hW (n - 1) (by omega))
    (supportedInjectiveHomology_isZero_of_forall_two_le_coheight X W hW n (by omega))
    (supportedInjectiveHomology_isZero_of_forall_two_le_coheight X (W ⊓ Z) hWZ n (by omega))
    (supportedInjectiveHomology_isZero_of_forall_two_le_coheight X (W ⊓ Z) hWZ (n + 1)
      (by omega))

/-- **Enlarging a support by a codimension-two set is bijective on `H^n`, `n ≤ 2`.** -/
theorem enlargeSupportedInjectiveHomology_bijective_of_codimTwo'
    (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z')
    (hcod : ∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z) (n : ℤ) (hn : n ≤ 2) :
    Function.Bijective
      (enlargeSupportedInjectiveHomology X (analyticClosedSupport_le_of_le X hZZ') n) := by
  obtain ⟨W, hWZ', hZ', hW⟩ := exists_closeds_sup_of_codimTwo X Z Z' hZZ' hcod
  exact enlargeSupportedInjectiveHomology_bijective_of_sup X hZZ' hWZ' hZ' hW n hn

/-- **Enlarging a support by a codimension-two set is bijective on `H²`.** If `Z ⊆ Z'` are
Zariski-closed and every point of `Z' ∖ Z` has coheight — codimension — at least two, then
`H²_{Z^an}(X^an, ℚ) → H²_{Z'^an}(X^an, ℚ)` is bijective. -/
theorem enlargeSupportedInjectiveHomology_bijective_of_codimTwo
    (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z')
    (hcod : ∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z) :
    Function.Bijective
      (enlargeSupportedInjectiveHomology X (analyticClosedSupport_le_of_le X hZZ')
        (2 * ((1 : ℕ) : ℤ))) :=
  enlargeSupportedInjectiveHomology_bijective_of_codimTwo' X Z Z' hZZ' hcod _ (by norm_num)

/-- **Descending a class along a codimension-two enlargement.** Every degree-two class supported
on `Z'^an` is the enlargement of a class supported on `Z^an`, with the same ordinary class. -/
theorem exists_enlarge_eq_of_codimTwo
    (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z')
    (hcod : ∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z)
    (β' : SupportedInjectiveHomology X (analyticClosedSupport X Z') (2 * ((1 : ℕ) : ℤ))) :
    ∃ β : SupportedInjectiveHomology X (analyticClosedSupport X Z) (2 * ((1 : ℕ) : ℤ)),
      enlargeSupportedInjectiveHomology X (analyticClosedSupport_le_of_le X hZZ')
          (2 * ((1 : ℕ) : ℤ)) β = β' ∧
        supportedInjectiveToAmbient X (analyticClosedSupport X Z) (2 * ((1 : ℕ) : ℤ)) β =
          supportedInjectiveToAmbient X (analyticClosedSupport X Z') (2 * ((1 : ℕ) : ℤ)) β' := by
  obtain ⟨β, hβ⟩ :=
    (enlargeSupportedInjectiveHomology_bijective_of_codimTwo X Z Z' hZZ' hcod).2 β'
  exact ⟨β, hβ, by rw [← hβ, supportedInjectiveToAmbient_enlarge]⟩

end AlgebraicGeometry.ComplexPoint
