import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirstTrace
import LeanCondensedMatter.Combinatorics.PerfectPairing
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# The general finite-mode Bloch–de Dominicis theorem (statement only — proof not yet started)

**Work in progress**: this file states the target of Phase 9's finite-mode Bloch–de Dominicis
induction (`notes/roadmaps/second-quantization.md`) — the `n`-point generalization of
`GibbsExpectation.lean`'s `gibbsExpectation_four_point` (`n = 2`) — but does **not** prove it yet
(`gibbsExpectation_prodComp_eq_sum_pairing`'s body is `sorry`). This is deliberately committed as a
`stated`-status target (per this project's `idea → stated → proved` convention,
`notes/roadmap.md`) to fix the API surface — the exact shape of the operator family, its
hypotheses, and the theorem statement — before attempting the induction itself, which is expected
to be the largest single proof in this project so far.

## The intended proof strategy

By strong induction on `n`, following the physics reference notes'
(`quantum-statistical-mechanics.tex`'s Bloch–De Dominicis theorem) proof: peel `C₀` off the front
of the product via `PeelFirstTrace.lean`'s `tsumTrace_diagonalEvolution_comp_peel`/
`traceFock_diagonalEvolution_comp_peel` (giving, after dividing by the partition function, a sum
of `gibbsExpectation (C₀.comp (Cⱼ)) * gibbsExpectation (remaining 2n-2 operators, Cⱼ erased)`
terms — matching `PeelFirst.lean`'s `peelTerms`, one term per position `j`), apply the inductive
hypothesis to each `(2n-2)`-operator remaining product (giving a `Pairing (n-1)` sum for it), and
reassemble into a `Pairing n` sum via `Combinatorics.PerfectPairing`'s
`Pairing.insertFirstPair`/`Pairing.equivSigma` — the combinatorial API built specifically for this
step (see `Combinatorics/PerfectPairing.lean`'s module docstring: "gives the later Bloch–de
Dominicis induction direct access to the unique partner of every operator position").

## Design notes on the statement below

- The `2n` operators are represented as a family `C : Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ]
  AlgebraicFock Config`, each with its own imaginary-time eigenvalue shift `q : Fin (2 * n) → ℝ`
  (`hC`) — unlike `TwoPoint.lean`/`FourPointReduction.lean`, which only needed the *first*
  operator's eigenvalue shift (since the c-number commutator handles the rest structurally), here
  *every* operator's shift is needed because the target product ranges over *arbitrary* pairs
  `(i, j)`, not just pairs involving a fixed first operator.
- The pairwise `ζ`-commutator coefficients are a family `c : Fin (2 * n) → Fin (2 * n) → ℂ`
  (`hcomm`), one c-number per ordered pair of distinct positions — the natural generalization of
  `TwoPoint.lean`'s single `c₁ⱼ`.
- The target states the product over `Pairing n`'s pairs directly in terms of
  `gibbsExpectation (C i .comp C j)` (matching `gibbsExpectation_four_point`'s own style) rather
  than the raw `c i j`/`(1 - ζw_i)` — cleaner, and what a caller actually wants, though it does mean
  the *statement* itself doesn't spell out that each factor reduces to `c i j / (1 - ζ w_i)` (that
  reduction is `TwoPoint.lean`'s `gibbsExpectation_comp_eq_div_of_zetaCommutator`, applicable to
  any single pair once its hypotheses are in hand — not part of this statement).
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- **The composed product of an `n`-operator family**, `C 0 ∘ C 1 ∘ ⋯ ∘ C (n-1)`, via
`PeelFirst.lean`'s `prodComp` applied to `List.ofFn C`. -/
noncomputable def prodCompFamily {k : ℕ}
    (C : Fin k → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  prodComp (List.ofFn C)

/-- **The general finite-mode, finite-temperature Bloch–de Dominicis theorem** (statement only —
see the module docstring; not yet proved). Given `2n` operators `C i`, each with its own
imaginary-time eigenvalue shift `qᵢ` and pairwise `ζ`-commutator coefficients `c i j` (for
`i ≠ j`), the normalized `2n`-point Gibbs expectation of their product is the `ζ`-weighted sum,
over every perfect pairing of the `2n` positions, of the product of each pair's normalized 2-point
value. -/
theorem gibbsExpectation_prodComp_eq_sum_pairing (n : ℕ) (s : Statistics)
    (energy : Config → ℝ) (β : ℝ)
    (C : Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ)
    (hC : ∀ i, heisenbergEvolve energy (-β) (C i) =
      Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i)
    (hcomm : ∀ i j, i ≠ j → zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
      c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0) :
    gibbsExpectation energy β (prodCompFamily C) =
      ∑ pairing : Common.BlochDeDominicis.Pairing n,
        pairing.weight s * ∏ pr ∈ pairing.pairs, gibbsExpectation energy β ((C pr.1).comp (C pr.2))
    := by
  sorry

end Common
end SecondQuantization
