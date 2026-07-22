import LeanCondensedMatter.SecondQuantization.Fermionic.DysonPartitionSeries
import LeanCondensedMatter.Combinatorics.MomentCumulant

set_option linter.style.header false

/-!
# Dyson coefficients as `Finset`-indexed vertex moments

Step 6 (PR 2) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): the
type-level seam between the Dyson series (`ℕ`-indexed perturbation order) and Track B's moment
type (`Finset α → ℂ`, indexed by a finite vertex set). `dysonVertexMoment` is `S.card!` times the
*normalized* Dyson partition coefficient at `n := S.card`
(`normalizedDysonPartitionCoeff`), whose numerator is `dysonPartitionCoeff`, the free-Gibbs-
weighted trace of the operator-valued `dysonCoeff` — not `dysonCoeff` itself. This lets
`Combinatorics/DiagramConnectedness.lean`'s abstract `WeightedDiagramFamily` machinery eventually
be instantiated with a genuine vertex set `S` of interaction insertions rather than a bare
perturbation order.

**The `S.card.factorial` normalization is required, not cosmetic.**
`normalizePartitionSeries (dysonPartitionSeries ε β V)` — equivalently,
`normalizedDysonPartitionCoeff`'s own coefficients — is the *ordinary* power series `Z/Z₀ = Σₙ zₙ
λⁿ` (`dysonPartitionSeries` itself is un-normalized, with constant term `Z₀ :=
freePartitionFunction`, not `1`); finite-set partition combinatorics (Track B's
`Finpartition.momentFromCumulant`/`cumulantFromMoment`) is native to *exponential* generating
series, `Σₙ mₙ λⁿ/n!`. Matching the two conventions forces `mₙ = n! zₙ` — omitting the factorial
would give set-partition block products the wrong multinomial weighting once diagram families with
more than one vertex are built on top of this file (`Fermionic/QuarticInteraction.lean`,
`Fermionic/WickDiagram.lean`, later PRs in this plan).

**Not yet connected to `PowerSeries.log`'s coefficients.** `dysonVertexCumulant` is only
`Finpartition.cumulantFromMoment` applied to `dysonVertexMoment` — the finite-set combinatorial
cumulant, not (yet) identified with any coefficient of `dysonFormalLogPartitionFunction`. That
identification needs a separate finite-set-cumulant/`exp`-`log` bridge, deliberately out of scope
here (see `FormalLogPartitionFunction.lean`'s own "What remains" note).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The normalized Dyson partition coefficient**, `dysonPartitionCoeff / freePartitionFunction`
— dividing through by the (nonzero) zeroth-order term so `normalizedDysonPartitionCoeff ε β V 0 =
1` (`normalizedDysonPartitionCoeff_zero` below), matching a genuine moment's normalization at the
empty vertex set. -/
noncomputable def normalizedDysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) : ℂ :=
  dysonPartitionCoeff ε β V n / freePartitionFunction ε β

omit [LinearOrder Mode] in
@[simp]
theorem normalizedDysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedDysonPartitionCoeff ε β V 0 = 1 := by
  rw [normalizedDysonPartitionCoeff, dysonPartitionCoeff_zero,
    div_self (freePartitionFunction_ne_zero ε β)]

/-- **The Dyson vertex moment** on a finite vertex set `S`, `S.card! • normalizedDysonPartitionCoeff
S.card` — Track B's `Finset α → ℂ` moment type, obtained from the Dyson perturbation series by the
exponential-generating-series factorial normalization. -/
noncomputable def dysonVertexMoment {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (S : Finset α) : ℂ :=
  (S.card.factorial : ℂ) * normalizedDysonPartitionCoeff ε β V S.card

omit [LinearOrder Mode] in
@[simp]
theorem dysonVertexMoment_empty {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    dysonVertexMoment ε β V (∅ : Finset α) = 1 := by
  simp [dysonVertexMoment]

/-- **The Dyson vertex cumulant**: `Finpartition.cumulantFromMoment` applied to
`dysonVertexMoment` — the finite-set combinatorial cumulant of the Dyson vertex moment, via
Möbius inversion on the partition lattice (`MomentCumulant.lean`). Not yet identified with any
coefficient of `dysonFormalLogPartitionFunction` — see the module docstring. -/
noncomputable def dysonVertexCumulant {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (S : Finset α) : ℂ :=
  Finpartition.cumulantFromMoment (dysonVertexMoment ε β V) S

end SecondQuantization
