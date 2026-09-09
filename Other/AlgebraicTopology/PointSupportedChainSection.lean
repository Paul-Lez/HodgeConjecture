/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularChainSheafDerivedPushforward
public import Other.AlgebraicTopology.DerivedClosedSupportTruncation

/-!
# The literal point chain as an actually closed-supported section

A point has a specified singular zero-simplex with coefficient `1`. Sheafifying its
relative chain and applying the actual singleton closed-embedding support factor gives
a supported global zero-chain. Regrading makes it a cocycle in degree zero. This is an
actual chain representative with singleton support, not a supplied fundamental class.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [Field R] (X : TopCat.{u}) [T1Space X] (x : X)

/-- The actual singleton subspace used for the point's chain representative. -/
abbrev pointChainSource : TopCat.{u} := TopCat.of ({x} : Set X)

/-- Its actual inclusion into the ambient space. -/
def pointChainEmbedding : pointChainSource X x ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Singletons are closed in a `T₁` space, so the actual closed-chain pushforward applies. -/
theorem pointChainEmbedding_isClosedEmbedding : IsClosedEmbedding (pointChainEmbedding X x) :=
  IsClosed.isClosedEmbedding_subtypeVal isClosed_singleton

/-- The exact closed image is the singleton, not merely a larger ambient support. -/
lemma pointChainEmbedding_support :
    (closedEmbeddingSupport (pointChainEmbedding X x)
      (pointChainEmbedding_isClosedEmbedding X x) : Set X) = {x} := by
  ext y
  change (∃ z : ({x} : Set X), z.1 = y) ↔ y ∈ ({x} : Set X)
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩

/-- The literal zero-simplex of the singleton source. -/
def pointChainSourceSimplex : (TopCat.toSSet.obj (pointChainSource X x)) _⦋0⦌ :=
  (TopCat.toSSetObjEquiv (pointChainSource X x) _).symm
    (ContinuousMap.const _ ⟨x, Set.mem_singleton x⟩)

/-- The coefficient map onto the literal relative zero-chain, before sheafification. -/
def pointChainSourceRelativeSection :
    AddCommGrpCat.of R ⟶
      (singularChainPresheaf R (pointChainSource X x) 0).obj
        (op ((Opens.map (pointChainEmbedding X x)).obj ⊤)) :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    ((TopCat.toSSet.obj (pointChainSource X x)).ιChainComplex (pointChainSourceSimplex X x) ≫
      (relativeChainProjection R
        (TopPair.ofSubset
          (((Opens.map (pointChainEmbedding X x)).obj ⊤ : Opens (pointChainSource X x)) :
            Set (pointChainSource X x))ᶜ)).f 0)

/-- The sheafification unit applied to the literal source point chain, followed by the
canonical degree-zero regrading. Its target is the actual direct-image section group. -/
def pointChainSourceSheafSection :
    AddCommGrpCat.of R ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (pointChainEmbedding X x)).obj
        ((singularChainSheafCochainComplex R (pointChainSource X x)).X 0)).obj.obj (op ⊤) :=
  pointChainSourceRelativeSection R X x ≫
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (pointChainSource X x))
      (singularChainPresheaf R (pointChainSource X x) 0)).app
        (op ((Opens.map (pointChainEmbedding X x)).obj ⊤)) ≫
    (singularChainSheafCochainComplexXIso R (pointChainSource X x) 0).inv.hom.app
      (op ((Opens.map (pointChainEmbedding X x)).obj ⊤))

/-- The actual point-chain section supported on the precise singleton image. -/
def pointSupportedChainSection :
    AddCommGrpCat.of R ⟶
      (((TopCat.Sheaf.closedSupportSections X
        (closedEmbeddingSupport (pointChainEmbedding X x)
          (pointChainEmbedding_isClosedEmbedding X x))).mapHomologicalComplex (.up ℤ)).obj
            (singularChainSheafCochainComplex R X)).X 0 :=
  pointChainSourceSheafSection R X x ≫
    ((singularChainSheafCochainPushforwardWithClosedSupport (pointChainEmbedding X x) R
      (pointChainEmbedding_isClosedEmbedding X x)).f 0).hom.app (op ⊤)

/-- Forgetting support gives exactly the actual point-chain pushforward on sections. -/
@[reassoc]
lemma pointSupportedChainSection_inclusion :
    pointSupportedChainSection R X x ≫
      ((singularCochainClosedSupportInclusion R
        (closedEmbeddingSupport (pointChainEmbedding X x)
          (pointChainEmbedding_isClosedEmbedding X x))).f 0).hom.app (op ⊤) =
      pointChainSourceSheafSection R X x ≫
        ((singularChainSheafCochainPushforward (pointChainEmbedding X x) R
          (pointChainEmbedding_isClosedEmbedding X x)).f 0).hom.app (op ⊤) := by
  have h := congrArg (fun f => (f.f 0).hom.app (op ⊤))
    (singularChainSheafCochainPushforwardWithClosedSupport_inclusion
      (pointChainEmbedding X x) R (pointChainEmbedding_isClosedEmbedding X x))
  change _ ≫ _ = _ at h
  exact (Category.assoc _ _ _).trans (congrArg (fun f => pointChainSourceSheafSection R X x ≫ f) h)

/-- The point-chain section is an actual degree-zero cocycle: the regraded complex has
zero terms in positive degrees, so its outgoing differential vanishes. -/
def pointSupportedChainCocycle :
    (HomologicalComplex.single AddCommGrpCat.{u} (.up ℤ) 0).obj (AddCommGrpCat.of R) ⟶
      ((TopCat.Sheaf.closedSupportSections X
        (closedEmbeddingSupport (pointChainEmbedding X x)
          (pointChainEmbedding_isClosedEmbedding X x))).mapHomologicalComplex (.up ℤ)).obj
            (singularChainSheafCochainComplex R X) :=
  HomologicalComplex.mkHomFromSingle (pointSupportedChainSection R X x) (by
    intro k hk
    have hpos : 0 < k := by change (0 : ℤ) + 1 = k at hk; omega
    exact (CochainComplex.isZero_of_isStrictlyLE _ 0 k hpos).eq_of_tgt _ _)

/-- The actual cocycle's degree-zero coefficient is precisely the supported point section. -/
@[simp]
lemma pointSupportedChainCocycle_f_zero :
    (pointSupportedChainCocycle R X x).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (AddCommGrpCat.of R)).hom ≫
        pointSupportedChainSection R X x :=
  HomologicalComplex.mkHomFromSingle_f _ _

end AlgebraicTopology.Singular
