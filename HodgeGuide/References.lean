/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "References" =>

Each entry points to the part of the source that develops a construction used in the
formalization.

* Pierre Deligne,
  [*The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf#page=56),
  in *The Millennium Prize Problems*, Clay Mathematics Institute and American Mathematical
  Society, 2006, pp. 45–53. §1 (pp. 45–46): the Hodge filtration, the classes of algebraic cycles,
  Hodge classes, and the statement of the conjecture. P. 51: the truncated holomorphic de Rham
  complex $`F^p\Omega^\bullet_{\mathrm{hol}}`.

* The Stacks Project,
  [§50.7, “The Hodge filtration”](https://stacks.math.columbia.edu/tag/0FM7):
  $`F^pH^n_{\mathrm{dR}}` as the image of the hypercohomology of the truncation
  $`\sigma_{\ge p}\Omega^\bullet`.

* The Stacks Project,
  [§42.42, “Cycles of given codimension”](https://stacks.math.columbia.edu/tag/0FE2):
  cycles as combinations of generic points.

* The Stacks Project,
  [§20.21, “Cohomology with support in a closed subset”](https://stacks.math.columbia.edu/tag/0A39):
  sections with support, their derived functors, and the long exact sequence.

* Mark Goresky,
  [*Lecture Notes on Sheaves and Perverse Sheaves*](https://www.math.ias.edu/~goresky/pdf/all.pdf):
  §3.10 (p. 17), the de Rham complex as a resolution of the constant sheaf; §5.2 (p. 22),
  Borel–Moore homology and the orientation sheaf; §§7.14–7.15 (pp. 31–32), the exact sequence of a
  pair and the support triangle; §8.11 (p. 37), fundamental classes and Poincaré duality for
  pseudomanifolds; §§12.4–12.5 (p. 59), the Borel–Moore chain sheaf and the dualizing complex.

* John M. Lee,
  [*Introduction to Complex Manifolds*](https://sites.math.washington.edu/~lee/Books/ICM/gsm-244-prev.pdf#page=32),
  Proposition 1.49: the canonical orientation of a complex manifold, preserved by local
  biholomorphisms.

# Where the constructions live

* `HodgeConjecture/Definitions/AlgebraicGeometry/HolomorphicDeRham.lean` and
  `HodgeFiltration.lean`: the de Rham complex, hypercohomology, and the Hodge filtration;
* `Other/AlgebraicGeometry/CodimensionCycle.lean`,
  `HodgeConjecture/Definitions/AlgebraicGeometry/AlgebraicCycleSupport.lean`,
  and `CohomologyWithSupport.lean`: cycles, their supports, and cohomology with support;
* `HodgeConjecture/Definitions/AlgebraicGeometry/CycleComponentSmoothSupportCoclassSection.lean`
  and `CycleComponentSupportExtension.lean`: the class on the smooth locus and its extension
  across the singular locus;
* `HodgeConjecture/Lemmas/AlgebraicGeometry/ComplexSheafBorelMoore.lean` and
  `ComplexSheafBorelMooreRationalComparison.lean`: Borel–Moore homology and duality;
* `HodgeConjecture/Definitions/AlgebraicGeometry/CycleComponentSheafClass.lean`: the class of a
  subvariety;
* `Other/AlgebraicGeometry/SheafCycleClass.lean`: the maps on cycles;
* `HodgeConjecture/Definitions/LinearAlgebra/HodgeStructure.lean`: pure Hodge structures and the
  $`(p,p)` criterion.
