import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.Combinatorics.MomentCumulant

set_option linter.style.header false

/-!
# Dyson coefficients as `Finset`-indexed vertex moments

This file is the type-level seam between the Dyson series, indexed by perturbation order `ℕ`, and
finite-set moment/cumulant combinatorics, indexed by a labelled vertex set `Finset α`.

`dysonVertexMoment` is `S.card!` times the normalized Dyson partition coefficient at
`n := S.card`. Its numerator is `dysonPartitionCoeff`, the free-Gibbs-weighted trace of the
operator-valued `dysonCoeff`, not `dysonCoeff` itself.

**The `S.card.factorial` normalization is required, not cosmetic.**
`normalizePartitionSeries (dysonPartitionSeries ε β V)` is an ordinary power series
`Z/Z₀ = Σₙ zₙ λⁿ`, while finite-set partition combinatorics is naturally exponential-generating,
`Σₙ mₙ λⁿ/n!`. Matching the conventions forces `mₙ = n! zₙ`; omitting the factorial would give
set-partition block products the wrong multinomial weights.

`dysonVertexCumulant` is the finite-set cumulant of this moment. The general identification of such
cumulants with factorial-normalized formal-log coefficients is proved in
`Combinatorics/PowerSeriesCumulant.lean`. The Dyson specialization is
`factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_dysonVertexCumulant`, and the final quartic
connected-diagram coefficient theorem is in
`Fermionic/Diagrammatics/DysonLinkedClusterTheorem.lean`.
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
`dysonVertexMoment`, using Möbius inversion on the finite-set partition lattice. Its identification
with factorial-normalized coefficients of `dysonFormalLogPartitionFunction` is proved in
`Fermionic/Diagrammatics/DysonLinkedClusterTheorem.lean`. -/
noncomputable def dysonVertexCumulant {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (S : Finset α) : ℂ :=
  Finpartition.cumulantFromMoment (dysonVertexMoment ε β V) S

end SecondQuantization
