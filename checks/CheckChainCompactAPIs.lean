import Other.AlgebraicTopology.SingularChainPresheafFlasque
import Other.AlgebraicTopology.SingularCoefficientBaseChange
import Other.AlgebraicTopology.SingularSubdivisionCochainSheaf
import Mathlib.Topology.LocallyConstant.Basic

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open scoped Simplicial

#check Finsupp.lapply
#check Finsupp.filter
#check Finsupp.filterAddHom
#check Finsupp.filterLinearMap
#check Finsupp.filter_single_of_pos
#check Finsupp.filter_single_of_neg
#check Finsupp.single
#check Finsupp.onFinset
#check Finsupp.support
#check Finsupp.mem_support_iff
#check ModuleCat.ofHom
#check ModuleCat.Hom.hom
#check Cofork.IsColimit.desc
#check Cofork.IsColimit.π_desc
#check TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
#check TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
#check SSet.ιChainComplex
#check SSet.chainComplex_hom_ext
#check IsLocallyConstant.iff_exists_open
#check IsLocallyConstant.apply_eq_of_preconnectedSpace
#check convex_stdSimplex
#check Convex.isPreconnected
#check Convex.isPathConnected
#check isCompact_univ.elim_finite_subcover
#check Set.Finite.toFinset
#check Set.Finite.iUnion
#check Finset.biUnion
#check GrothendieckTopology.Plus.exists_rep
#check GrothendieckTopology.Plus.mk
#check GrothendieckTopology.Plus.toPlus_eq_mk
#check GrothendieckTopology.Plus.isSheaf_of_sep
#check plusPlusIsoSheafify
#check toSheafify_plusPlusIsoSheafify_hom
#check CategoryTheory.Presheaf.IsSheaf
#check TopCat.Presheaf.IsSheaf
#check TopPair.ofSubset
#check TopPair.fst
#check TopPair.map

example (X : TopCat) (s : Set X) : (TopPair.ofSubset (X := X) s).fst = X := rfl

example (R : Type) [Field R] (X : TopCat) (s : Set X) (n : ℕ) :
    ((chainPairFunctor R).obj (TopPair.ofSubset (X := X) s)).right.X n =
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n := rfl

example (n : ℕ) : PreconnectedSpace (stdSimplex ℝ (Fin (n+1))) := by infer_instance

example {X : TopCat} [CompactSpace X]
    (S : (Opens.grothendieckTopology X).Cover (⊤ : Opens X)) :
    ∃ t : Finset S.Arrow, Set.univ ⊆ ⋃ i ∈ t, (i.Y : Set X) := by
  apply isCompact_univ.elim_finite_subcover
  · exact fun i => i.Y.isOpen
  · simpa only [coveringSieveOpenFamily] using
      Set.Subset.rfl.trans_eq (coveringSieveOpenFamily_iUnion X S).symm
