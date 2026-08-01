import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.Combinatorics.MomentCumulant

set_option linter.style.header false

/-!
# Dyson coefficients as `Finset`-indexed vertex moments

This file is the seam between the Common Dyson trace series, indexed by perturbation order `ℕ`, and
finite-set moment/cumulant combinatorics, indexed by a labelled vertex set `Finset α`.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The normalized Common Dyson trace coefficient. -/
noncomputable def normalizedDysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) : ℂ :=
  Common.dysonTraceCoeff (fermionEnergy ε) β V n / freePartitionFunction ε β

omit [LinearOrder Mode] in
@[simp]
theorem normalizedDysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    normalizedDysonPartitionCoeff ε β V 0 = 1 := by
  rw [normalizedDysonPartitionCoeff, ← dysonPartitionCoeff_eq_dysonTraceCoeff,
    dysonPartitionCoeff_zero, div_self (freePartitionFunction_ne_zero ε β)]

/-- The factorial-normalized Dyson vertex moment on a finite vertex set. -/
noncomputable def dysonVertexMoment {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (S : Finset α) : ℂ :=
  (S.card.factorial : ℂ) * normalizedDysonPartitionCoeff ε β V S.card

omit [LinearOrder Mode] in
@[simp]
theorem dysonVertexMoment_empty {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    dysonVertexMoment ε β V (∅ : Finset α) = 1 := by
  simp [dysonVertexMoment]

/-- The finite-set cumulant of the Dyson vertex moment. -/
noncomputable def dysonVertexCumulant {α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (S : Finset α) : ℂ :=
  Finpartition.cumulantFromMoment (dysonVertexMoment ε β V) S

end SecondQuantization
