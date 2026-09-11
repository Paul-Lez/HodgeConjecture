/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernLocalModel
public import Other.AlgebraicGeometry.SupportUnionSplitting

/-!
# Excision in codimension one: the component support decomposition

This file proves `HasComponentSupportDecomposition X` (`Other/AlgebraicGeometry/ChernLocalModel.lean`,
§4.3 step 4 of `docs/DIVISOR_HANDOFF.md`) from a single vanishing statement in complex
codimension two, `HasCodimensionTwoSupportedVanishing X`.

The mathematical content is Mayer–Vietoris for two closed supports, proved in full generality in
`Other/AlgebraicGeometry/SupportUnionSplitting.lean`
(`TopCat.Sheaf.exists_supportedSectionsEnlarge_add_eq`): for closed sets `Z₁`, `Z₂` of a
topological space and termwise flasque coefficients, a degree-`n` class supported in `Z₁ ∪ Z₂` is
the sum of a class supported in `Z₁` and one supported in `Z₂` as soon as `H^{n+1}` with support
in `Z₁ ∩ Z₂` vanishes. Here it is applied, by induction on the finite set of components, to
`Z₁ = |Z_a|^an` and `Z₂ = |⋃_{y ∈ t} Z_y|^an`; the intersection is the analytic support of the
Zariski-closed set `Z_a ∩ ⋃_{y ∈ t} Z_y`, all of whose points have coheight — that is,
codimension — at least two, which is proved here
(`two_le_coheight_of_mem_closure_inter`, `coheight_of_mem_pairwiseZariskiSupport`).

What is left open is exactly the vanishing input: `HasCodimensionTwoSupportedVanishing X` says
that supported cohomology in degree three vanishes along the analytic support of a Zariski-closed
subset of codimension at least two (real codimension at least four). This is the general form of
the vanishing that the repository already proves for the singular boundary of a single component
(`cycleComponentSingularBoundarySectionCohomology_isZero_of_lt`), and it is the only obligation
used here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance componentSupportDecompositionAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### The analytic support of a Zariski-closed subset -/

/-- The analytic support of a Zariski-closed subset of `X.left`: the complex points lying over
it. It is closed in the analytic topology. -/
def analyticClosedSupport (W : Closeds X.left) : Closeds (ComplexPoint X) :=
  ⟨Point.underlying ⁻¹' (W : Set X.left), isClosed_complexPoint_underlying_preimage X W⟩

@[simp]
theorem mem_analyticClosedSupport {W : Closeds X.left} {z : ComplexPoint X} :
    z ∈ analyticClosedSupport X W ↔ Point.underlying z ∈ W := Iff.rfl

theorem analyticClosedSupport_bot : analyticClosedSupport X ⊥ = ⊥ := by
  ext z; exact Iff.rfl

theorem analyticClosedSupport_sup (W₁ W₂ : Closeds X.left) :
    analyticClosedSupport X (W₁ ⊔ W₂) =
      analyticClosedSupport X W₁ ⊔ analyticClosedSupport X W₂ := by
  ext z; exact Iff.rfl

theorem analyticClosedSupport_inf (W₁ W₂ : Closeds X.left) :
    analyticClosedSupport X (W₁ ⊓ W₂) =
      analyticClosedSupport X W₁ ⊓ analyticClosedSupport X W₂ := by
  ext z; exact Iff.rfl

/-- The analytic support of the closure of a point is the analytic support of the corresponding
cycle component. -/
theorem analyticClosedSupport_closure (x : X.left) :
    analyticClosedSupport X ⟨closure {x}, isClosed_closure⟩ =
      cycleComponentAnalyticClosedSupport X x := rfl

/-- The Zariski support of a finite family of points: the union of the closures. -/
def componentsZariskiSupport (s : Finset X.left) : Closeds X.left :=
  s.sup fun x => ⟨closure {x}, isClosed_closure⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem mem_componentsZariskiSupport {s : Finset X.left} {z : X.left} :
    z ∈ componentsZariskiSupport X s ↔ ∃ x ∈ s, z ∈ closure ({x} : Set X.left) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [componentsZariskiSupport, Finset.sup_empty]
      exact ⟨fun h => absurd h (id : z ∈ (⊥ : Closeds X.left) → False),
        fun ⟨_, hy, _⟩ => absurd hy (Finset.notMem_empty _)⟩
  | insert a s ha ih =>
      have hsup : z ∈ componentsZariskiSupport X (insert a s) ↔
          z ∈ closure ({a} : Set X.left) ∨ z ∈ componentsZariskiSupport X s := by
        rw [componentsZariskiSupport, Finset.sup_insert]
        exact Iff.rfl
      rw [hsup, ih]
      constructor
      · rintro (h | ⟨y, hy, hz⟩)
        · exact ⟨a, Finset.mem_insert_self a s, h⟩
        · exact ⟨y, Finset.mem_insert_of_mem hy, hz⟩
      · rintro ⟨y, hy, hz⟩
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Or.inl hz
        · exact Or.inr ⟨y, hy, hz⟩

theorem analyticClosedSupport_componentsZariskiSupport (s : Finset X.left) :
    analyticClosedSupport X (componentsZariskiSupport X s) =
      componentsAnalyticClosedSupport X s := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [componentsZariskiSupport, Finset.sup_empty, analyticClosedSupport_bot,
        componentsAnalyticClosedSupport, Finset.sup_empty]
  | insert a s ha ih =>
      rw [componentsZariskiSupport, Finset.sup_insert,
        analyticClosedSupport_sup, analyticClosedSupport_closure,
        show (s.sup fun x : X.left => (⟨closure {x}, isClosed_closure⟩ : Closeds X.left)) =
          componentsZariskiSupport X s from rfl, ih]
      exact (Finset.sup_insert).symm

/-! ### Two distinct prime divisors meet in codimension at least two -/

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- A point in the closures of two distinct codimension-one points has codimension at least two:
it is a proper specialization of at least one of them. -/
theorem two_le_coheight_of_mem_closure_inter {x y z : X.left}
    (hx : coheight x = ((1 : ℕ) : ℕ∞)) (hy : coheight y = ((1 : ℕ) : ℕ∞)) (hxy : x ≠ y)
    (hzx : z ∈ closure ({x} : Set X.left)) (hzy : z ∈ closure ({y} : Set X.left)) :
    (2 : ℕ∞) ≤ coheight z := by
  have hzx' : z ≤ x := specializes_iff_mem_closure.mpr hzx
  have hzy' : z ≤ y := specializes_iff_mem_closure.mpr hzy
  by_cases h1 : z < x
  · calc (2 : ℕ∞) = coheight x + 1 := by rw [hx]; rfl
      _ ≤ coheight z := Order.coheight_add_one_le h1
  by_cases h2 : z < y
  · calc (2 : ℕ∞) = coheight y + 1 := by rw [hy]; rfl
      _ ≤ coheight z := Order.coheight_add_one_le h2
  exfalso
  have hxz : x ≤ z := by
    by_contra hc
    exact h1 (lt_of_le_not_ge hzx' hc)
  have hyz : y ≤ z := by
    by_contra hc
    exact h2 (lt_of_le_not_ge hzy' hc)
  have hyx : y ≤ x := hyz.trans hzx'
  have hxy' : x ≤ y := hxz.trans hzy'
  have h₁ : x ⤳ y := hyx
  have h₂ : y ⤳ x := hxy'
  exact hxy (Specializes.antisymm h₁ h₂).eq

/-! ### The vanishing obligation -/

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The empty support carries no cohomology: the supported-section complex is the zero
complex. -/
theorem isZero_supportedInjectiveHomology_bot (n : ℤ) :
    IsZero (SupportedInjectiveHomology X ⊥ n) := by
  have h : (⊥ : Closeds (ComplexPoint X)).compl = ⊤ := by ext z; simp
  show IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)).obj (((TopCat.Sheaf.sheafSectionsSupportedOutside (TopCat.of (ComplexPoint X))
      (⊥ : Closeds (ComplexPoint X)).compl).mapHomologicalComplex (.up ℤ)).obj
        (ambientRationalInjectiveComplex X))).homology n)
  rw [h]
  exact TopCat.Sheaf.supportedSections_top_homology_isZero _ ⊤ _ n

/-- **Obligation: vanishing of supported cohomology in complex codimension two.** If every point
of a Zariski-closed subset `W` of `X.left` has coheight — that is, codimension — at least two,
then the rational cohomology of `X^an` with support in the analytic support of `W` vanishes in
degree three.

This is the general form of the vanishing that the repository already proves for the singular
boundary of a single cycle component
(`cycleComponentSingularBoundarySectionCohomology_isZero_of_lt`,
`Other/AlgebraicGeometry/CycleComponentSupportExtension.lean`): such a `W` is covered by a finite
smooth stratification whose strata have real dimension at most `2 dim X - 4`, and supported
cohomology vanishes below the real codimension, so in fact all degrees `< 4` vanish. Only degree
three is used here, through the connecting map of the Mayer–Vietoris sequence. -/
def HasCodimensionTwoSupportedVanishing : Prop :=
  ∀ W : Closeds X.left, (∀ z ∈ W, (2 : ℕ∞) ≤ coheight z) →
    IsZero (SupportedInjectiveHomology X (analyticClosedSupport X W) (2 * ((1 : ℕ) : ℤ) + 1))

/-! ### Excision in codimension one -/

set_option maxHeartbeats 1000000 in
/-- **Excision in codimension one.** A degree-two rational class supported on the analytic
support of a finite set of prime divisors is the sum of classes supported on the individual
components.

The induction step is Mayer–Vietoris for the two closed supports `|Z_a|^an` and
`|⋃_{y ∈ t} Z_y|^an` (`TopCat.Sheaf.exists_supportedSectionsEnlarge_add_eq`); their intersection
is the analytic support of a Zariski-closed subset of codimension at least two, so the only input
is `HasCodimensionTwoSupportedVanishing X`. -/
theorem hasComponentSupportDecomposition (hvan : HasCodimensionTwoSupportedVanishing X) :
    HasComponentSupportDecomposition X := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _ β
      refine ⟨fun _ => 0, ?_⟩
      rw [Finset.sum_empty]
      have hz : IsZero (SupportedInjectiveHomology X
          (componentsAnalyticClosedSupport X (∅ : Finset X.left)) (2 * ((1 : ℕ) : ℤ))) := by
        rw [show componentsAnalyticClosedSupport X (∅ : Finset X.left) = ⊥ from Finset.sup_empty]
        exact isZero_supportedInjectiveHomology_bot X _
      simpa using ConcreteCategory.congr_hom (hz.eq_of_src (𝟙 _) 0) β
  | insert a t ha ih =>
      intro hco β
      have hco' : ∀ x ∈ t, coheight x = ((1 : ℕ) : ℕ∞) :=
        fun x hx => hco x (Finset.mem_insert_of_mem hx)
      have hcoa : coheight a = ((1 : ℕ) : ℕ∞) := hco a (Finset.mem_insert_self a t)
      have hins : componentsAnalyticClosedSupport X (insert a t) =
          cycleComponentAnalyticClosedSupport X a ⊔ componentsAnalyticClosedSupport X t :=
        Finset.sup_insert
      have hle₁ : cycleComponentAnalyticClosedSupport X a ≤
          componentsAnalyticClosedSupport X (insert a t) :=
        cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X
          (Finset.mem_insert_self a t)
      have hle₂ : componentsAnalyticClosedSupport X t ≤
          componentsAnalyticClosedSupport X (insert a t) := by
        rw [hins]; exact le_sup_right
      have h₁ : (componentsAnalyticClosedSupport X (insert a t)).compl ≤
          (cycleComponentAnalyticClosedSupport X a).compl := fun _ hx hz => hx (hle₁ hz)
      have h₂ : (componentsAnalyticClosedSupport X (insert a t)).compl ≤
          (componentsAnalyticClosedSupport X t).compl := fun _ hx hz => hx (hle₂ hz)
      have hmeet : (cycleComponentAnalyticClosedSupport X a).compl ⊓
          (componentsAnalyticClosedSupport X t).compl ≤
          (componentsAnalyticClosedSupport X (insert a t)).compl := by
        intro z hz hmem
        rw [hins] at hmem
        exact hmem.elim (fun h => hz.1 h) (fun h => hz.2 h)
      have h₁' : (cycleComponentAnalyticClosedSupport X a).compl ≤
          (cycleComponentAnalyticClosedSupport X a ⊓
            componentsAnalyticClosedSupport X t).compl := fun _ hx hz => hx hz.1
      have h₂' : (componentsAnalyticClosedSupport X t).compl ≤
          (cycleComponentAnalyticClosedSupport X a ⊓
            componentsAnalyticClosedSupport X t).compl := fun _ hx hz => hx hz.2
      have hcover : (cycleComponentAnalyticClosedSupport X a ⊓
            componentsAnalyticClosedSupport X t).compl ≤
          (cycleComponentAnalyticClosedSupport X a).compl ⊔
            (componentsAnalyticClosedSupport X t).compl := by
        intro z hz
        by_cases hz₁ : z ∈ cycleComponentAnalyticClosedSupport X a
        · exact Or.inr (fun hz₂ => hz ⟨hz₁, hz₂⟩)
        · exact Or.inl hz₁
      have hvanZ : IsZero (SupportedInjectiveHomology X
          (cycleComponentAnalyticClosedSupport X a ⊓ componentsAnalyticClosedSupport X t)
          (2 * ((1 : ℕ) : ℤ) + 1)) := by
        have hW : analyticClosedSupport X
            (⟨closure {a}, isClosed_closure⟩ ⊓ componentsZariskiSupport X t) =
            cycleComponentAnalyticClosedSupport X a ⊓ componentsAnalyticClosedSupport X t := by
          rw [analyticClosedSupport_inf, analyticClosedSupport_closure,
            analyticClosedSupport_componentsZariskiSupport]
        rw [← hW]
        refine hvan _ (fun z hz => ?_)
        obtain ⟨y, hy, hzy⟩ := (mem_componentsZariskiSupport X).mp hz.2
        refine two_le_coheight_of_mem_closure_inter X hcoa (hco' y hy) ?_ hz.1 hzy
        rintro rfl
        exact ha hy
      obtain ⟨α₁, α₂, hsum⟩ := TopCat.Sheaf.exists_supportedSectionsEnlarge_add_eq
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X a).compl
        (componentsAnalyticClosedSupport X t).compl
        (componentsAnalyticClosedSupport X (insert a t)).compl
        (cycleComponentAnalyticClosedSupport X a ⊓ componentsAnalyticClosedSupport X t).compl
        h₁ h₂ hmeet h₁' h₂' hcover (ambientRationalInjectiveComplex X)
        (fun j => TopCat.Sheaf.injective_isFlasque _ _) (2 * ((1 : ℕ) : ℤ))
        (2 * ((1 : ℕ) : ℤ) + 1) rfl hvanZ β
      obtain ⟨γ', hγ'⟩ := ih hco' α₂
      refine ⟨Function.update γ' a α₁, ?_⟩
      rw [Finset.sum_insert ha]
      have hupd_a : (Function.update γ' a α₁) a = α₁ := Function.update_self ..
      have hupd : ∀ x ∈ t, (Function.update γ' a α₁) x = γ' x := by
        intro x hx
        have hne : x ≠ a := by rintro rfl; exact ha hx
        exact Function.update_of_ne hne _ _
      have key₁ : componentContribution X (insert a t) a (2 * ((1 : ℕ) : ℤ)) α₁ =
          enlargeSupportedInjectiveHomology X hle₁ (2 * ((1 : ℕ) : ℤ)) α₁ :=
        componentContribution_of_mem X (Finset.mem_insert_self a t) _ α₁
      have key₂ : ∀ x ∈ t, componentContribution X (insert a t) x (2 * ((1 : ℕ) : ℤ))
            (Function.update γ' a α₁ x) =
          enlargeSupportedInjectiveHomology X hle₂ (2 * ((1 : ℕ) : ℤ))
            (componentContribution X t x (2 * ((1 : ℕ) : ℤ)) (γ' x)) := by
        intro x hx
        rw [hupd x hx, componentContribution_of_mem X (Finset.mem_insert_of_mem hx),
          componentContribution_of_mem X hx]
        exact (TopCat.Sheaf.supportedSectionsEnlarge_comp (TopCat.of (ComplexPoint X))
          (ambientRationalInjectiveComplex X) _ _ (2 * ((1 : ℕ) : ℤ)) (γ' x)).symm
      rw [Finset.sum_congr rfl key₂, hupd_a, key₁, ← map_sum, ← hγ']
      exact hsum

/-- **The step-4 assembly, with the decomposition obligation discharged.** Combined with
`hasDivisorOfAlgebraicModel_of_divisorClass`, the remaining obligation
`HasDivisorClassOfSomeCartierData X` of `docs/DIVISOR_HANDOFF.md` §3 now follows from the
codimension-two vanishing and the local model. -/
theorem hasDivisorClassOfSomeCartierData_of_localModel_of_vanishing
    (hvan : HasCodimensionTwoSupportedVanishing X) (hloc : HasChernLocalModel X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_localModel X
    (hasComponentSupportDecomposition X hvan) hloc

end AlgebraicGeometry.ComplexPoint
