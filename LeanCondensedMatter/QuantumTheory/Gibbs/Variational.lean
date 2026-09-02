import LeanCondensedMatter.QuantumTheory.Gibbs.Entropy
import LeanCondensedMatter.QuantumTheory.Entropy.Finite

/-!
# Gibbs-state variational equality

The normalized Gibbs state attains the Helmholtz lower bound. Under the bounded-Hamiltonian API,
compactness of `exp (-βH)` forces finite dimensionality, so the dimension-independent Gibbs-diagonal
entropy identity applies to a common energy eigenbasis.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gibbs state has finite entropy and satisfies `S(ρβ) = β E(ρβ) + log Z`. -/
theorem vonNeumannEntropy_gibbsState (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    vonNeumannEntropy (gibbsState Hop β hcompact hZ) ≠ ⊤ ∧
      (vonNeumannEntropy (gibbsState Hop β hcompact hZ)).toReal =
        β * energyExpValue (gibbsState Hop β hcompact hZ) Hop +
          Real.log (spectralTrace (gibbsOp Hop β)) := by
  classical
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  let ρ := gibbsState Hop β hcompact hZ
  let Z : ℝ := spectralTrace (gibbsOp Hop β)
  let E : Fin (Module.finrank ℂ H) → ℝ :=
    Hop.2.isSymmetric.eigenvalues rfl
  let bE : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    Hop.2.isSymmetric.eigenvectorBasis rfl
  have hEbE (i : Fin (Module.finrank ℂ H)) :
      (Hop.1 : H →ₗ[ℂ] H) (bE i) = (E i : ℂ) • bE i := by
    simpa [E, bE] using Hop.2.isSymmetric.apply_eigenvectorBasis rfl i
  have hZpos : 0 < Z := by
    simpa [Z] using spectralTrace_gibbsOp_pos Hop β hZ
  have hρbE (i : Fin (Module.finrank ℂ H)) :
      (ρ.op : H →ₗ[ℂ] H) (bE i) =
        ((Real.exp (-β * E i) / Z : ℝ) : ℂ) • bE i := by
    simpa [ρ, Z, div_eq_mul_inv, mul_comm] using
      (gibbsState_apply_eigenvector Hop β hcompact hZ (hEbE i))
  change vonNeumannEntropy ρ ≠ ⊤ ∧
    (vonNeumannEntropy ρ).toReal = β * energyExpValue ρ Hop + Real.log Z
  exact vonNeumannEntropy_gibbs_diagonal ρ Hop bE.toHilbertBasis E β Z hZpos
    (fun i => by simpa using hρbE i) (fun i => by simpa using hEbE i)
    ρ.entropyOp_hasSummableRealEigenvalues

/-- For nonzero inverse temperature, the normalized Gibbs state satisfies the exact Helmholtz
free-energy identity. -/
theorem gibbsState_helmholtzFreeEnergy_eq (Hop : Observable H) (β : ℝ) (hβ : β ≠ 0)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    energyExpValue (gibbsState Hop β hcompact hZ) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β hcompact hZ)).toReal =
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β)) := by
  have hEntropy :=
    (vonNeumannEntropy_gibbsState Hop β hcompact hZ).2
  rw [hEntropy, mul_add]
  have hscale :
      (1 / β) *
          (β * energyExpValue (gibbsState Hop β hcompact hZ) Hop) =
        energyExpValue (gibbsState Hop β hcompact hZ) Hop := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hβ, one_mul]
  rw [hscale]
  ring

/-- Every density operator has Helmholtz free energy at least that of the normalized Gibbs state. -/
theorem gibbsState_minimizes_helmholtzFreeEnergy (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    energyExpValue (gibbsState Hop β hcompact hZ) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β hcompact hZ)).toReal ≤
      energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal := by
  rw [gibbsState_helmholtzFreeEnergy_eq Hop β hβ.ne' hcompact hZ]
  exact (helmholtzFreeEnergy_ge_and_entropy_ne_top
    ρ Hop β hβ hcompact hZ).2

end QuantumTheory
