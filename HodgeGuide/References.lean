/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "References" =>

These are not generic background suggestions. Each item points to the part that develops a
construction used in the formalization.

* Pierre Deligne,
  [*The Hodge Conjecture*](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf),
  especially §1 and pp. 45--46: rational Hodge classes, Poincaré-dual cycle classes, the
  conjecture, and the Hodge filtration; p. 51 displays the truncated holomorphic de Rham complex.

* The Stacks Project,
  [§50.7, “The Hodge filtration”](https://stacks.math.columbia.edu/tag/0FM7): the Hodge
  filtration as the image of hypercohomology of the stupid truncation in the full de Rham
  hypercohomology.

* The Stacks Project,
  [§42.42, “Cycles of given codimension”](https://stacks.math.columbia.edu/tag/0FE2)
  and [§42.19, “Rational equivalence”](https://stacks.math.columbia.edu/tag/02RW): cycles by
  generic points and rational equivalence through principal divisors and proper pushforward.

* The Stacks Project,
  [§20.21, “Cohomology with support in a closed subset”](https://stacks.math.columbia.edu/tag/0A39):
  sections with support, derived cohomology with support, and the associated long exact sequence.

* Mark Goresky,
  [*Lecture Notes on Sheaves and Perverse Sheaves*](https://www.math.ias.edu/~goresky/pdf/all.pdf):
  §§3.10--3.11 for the sheaf de Rham resolution; §§5.2--5.3 for Borel--Moore chains, local
  orientations, and compactification-relative homology; §§7.14--7.15 for support triangles and
  relative cohomology; §§8.10--8.11 for pseudomanifold fundamental classes; and §§12.4--12.6 for
  the Borel--Moore chain sheaf, dualizing complex, and Verdier-duality viewpoint.

* John M. Lee,
  [*Introduction to Complex Manifolds*, Proposition 1.49](https://sites.math.washington.edu/~lee/Books/ICM/gsm-244-prev.pdf#page=32):
  the canonical orientation of a complex manifold and preservation of orientation by holomorphic
  transition maps.

# Source cross-reference

The relevant repository files are:

* `Definitions/AlgebraicGeometry/HolomorphicDeRham.lean` and `HodgeFiltration.lean` for the first
  two references;
* `Definitions/AlgebraicGeometry/ChowGroup.lean`, `AlgebraicCycleSupport.lean`, and
  `CohomologyWithSupport.lean` for the next two;
* `Other/AlgebraicGeometry/CycleComponentSmoothSupportCoclassSection.lean` and
  `CycleComponentSupportExtension.lean` for the normalized smooth-locus class and its extension
  across the singular boundary;
* `Other/AlgebraicGeometry/ComplexSheafBorelMoore.lean`,
  `ComplexSheafBorelMooreRationalComparison.lean`, and `CycleComponentSheafClass.lean` for the
  actual ambient chain-sheaf construction, smooth-ambient duality, and normalized component class;
* `Other/AlgebraicGeometry/SheafCycleClass.lean` for the additive and rational-linear maps on
  cycles;
* `Definitions/LinearAlgebra/HodgeStructure.lean` for the pure-Hodge-structure calculation behind
  the rational $`F^p` criterion.

This website is built with [Verso](https://github.com/leanprover/verso). Its Lean snippets are
elaborated as part of the build, linking the exposition to the checked declarations rather than
copying an unchecked API listing.
