import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.MatrixEvaluation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.OperatorPeel
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Bloch–de Dominicis theorem

The shared finite-temperature theory is organized into reusable layers:

- `PairingWeight`: the statistics-dependent crossing factor used by general pairing expansions;
- `ExpectationRecursion`: the basis-, representation-, and implementation-independent normalized
  expectation/KMS contract for a general even pairing sum;
- `MatrixEvaluation`: the preferred number-conserving backend, where bipartite contractions are
  evaluated by Mathlib determinants for fermions and permanents for bosons;
- `OperatorPeel`: the representation-independent finite operator-exchange identity preceding KMS
  rotation;
- `Unnormalized` and `GibbsExpectation`: concrete operator, trace-ratio, and finite Gibbs identities;
- `Induction`: the finite Gibbs specialization of the generic pairing theorem where the fully
  general pairing representation is still required.

For number-conserving free thermal states, same-type contractions vanish, so the matrix backend is
strictly smaller than enumerating all perfect pairings: the surviving bipartite pairings are indexed
by permutations.  `MatrixEvaluation` uses Mathlib's determinant Laplace expansion directly and
provides the corresponding permanent row expansion once.  The project `Pairing` type remains the
right representation for genuine Wick-diagram connectivity, crossings, components, and relabeling.

The generic recursion has no configuration type or `Fintype` assumption. Its `admissible` predicate
remains available for applications that genuinely need a general Gaussian/quasi-free pairing sum.
Finite occupation-basis formulas live outside this hierarchy behind explicit bridges.
-/
