import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Trace

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Axiomatic quantum theory: mixed states and the Born rule

Formalizes the density-operator postulate and general (POVM) measurement postulate,
extending `QuantumTheory.State`/`QuantumTheory.Observable` from
`LeanCondensedMatter/QuantumTheory/Postulates.lean` to mixed states.

**Scope note:** restricted to finite-dimensional `H`. Mathlib currently has no
trace-class / Schatten-class operator theory, so `LinearMap.trace` (which requires
finite-dimensionality) is the only trace available; extending to the
countably-infinite-dimensional lattice setting used elsewhere in this project needs
that machinery first. See `notes/caveats.md`.
-/

namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **Density operator postulate.** The state of a quantum system (allowing statistical
mixtures, not just pure states) is a positive operator of trace 1. -/
def DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] :=
  { ρ : H →L[ℂ] H // ρ.IsPositive ∧ LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1 }

/-- A (finite-outcome) POVM: a finite family of positive operators summing to the identity. -/
structure POVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (M : Type*) [Fintype M] where
  E : M → H →L[ℂ] H
  pos : ∀ m, (E m).IsPositive
  sum_eq_id : (∑ m, E m) = ContinuousLinearMap.id ℂ H

variable {M : Type*} [Fintype M]

/-- **Born rule (general measurement postulate).** The probability of obtaining outcome `m`
of a POVM measurement `P` on a state `ρ` is `Tr[E_m ρ]`. -/
noncomputable def prob (P : POVM H M) (ρ : DensityOperator H) (m : M) : ℝ :=
  (LinearMap.trace ℂ H ((P.E m ∘L (ρ.1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)).re

/-- The outcome probabilities of a POVM measurement sum to `1`, as required for `prob` to be a
genuine probability distribution over outcomes. -/
theorem sum_prob_eq_one (P : POVM H M) (ρ : DensityOperator H) :
    ∑ m, prob P ρ m = 1 := by
  have hsum : (∑ m, P.E m ∘L (ρ.1 : H →L[ℂ] H)) = (ρ.1 : H →L[ℂ] H) := by
    rw [← ContinuousLinearMap.finsetSum_comp (s := (Finset.univ : Finset M)) P.E
      (ρ.1 : H →L[ℂ] H), P.sum_eq_id, ContinuousLinearMap.id_comp]
  simp only [prob, ← Complex.re_sum, ← map_sum, ← ContinuousLinearMap.toLinearMap_sum, hsum]
  simp [ρ.2.2]

/-- **Pure-state density-operator embedding.** A pure state `ψ` gives rise to a density operator,
the rank-one projector `|ψ⟩⟨ψ|`; this is the density-operator picture's counterpart of
`QuantumTheory.State`. This is not a purification of a mixed state: purification is reserved for
representing a mixed state as the reduced state of a pure state on a larger Hilbert space. -/
noncomputable def pure (ψ : State H) : DensityOperator H :=
  ⟨InnerProductSpace.rankOne ℂ ψ.1 ψ.1, InnerProductSpace.isPositive_rankOne_self ψ.1, by
    rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, ψ.2]; norm_num⟩

/-- The purity of a density operator, `Tr[ρ²]`. -/
noncomputable def purity (ρ : DensityOperator H) : ℂ :=
  LinearMap.trace ℂ H ((ρ.1 ∘L (ρ.1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)

/-- A pure state (in the sense of `pure`) has purity `1`, distinguishing it from a genuine
statistical mixture. -/
theorem purity_pure (ψ : State H) : purity (pure ψ) = 1 := by
  simp [purity, pure, InnerProductSpace.rankOne_comp_rankOne,
    InnerProductSpace.trace_rankOne, ψ.2]

end QuantumTheory
