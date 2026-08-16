import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointEntropy

/-!
# Gibbs-state variational equality

The normalized Gibbs state attains the Helmholtz lower bound. Under the bounded-Hamiltonian API,
compactness of `exp (-βH)` forces finite dimensionality, so the generic pure-point Gibbs entropy
identity applies to a common energy eigenbasis.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gibbs state has finite entropy and satisfies `S(ρβ) = β E(ρβ) + log Z`. -/
theorem vonNeumannEntropy_gibbsState (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    vonNeumannEntropy (gibbsState Hop β hcompact hsummable hZ) ≠ ⊤ ∧
      (vonNeumannEntropy (gibbsState Hop β hcompact hsummable hZ)).toReal =
        β * energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop +
          Real.log (spectralTrace (gibbsOp Hop β)) := by
  classical
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  let ρ := gibbsState Hop β hcompact hsummable hZ
  let E : Fin (Module.finrank ℂ H) → ℝ :=
    Hop.2.isSymmetric.eigenvalues rfl
  let bE : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    Hop.2.isSymmetric.eigenvectorBasis rfl
  have hEbE (i : Fin (Module.finrank ℂ H)) :
      (Hop.1 : H →ₗ[ℂ] H) (bE i) = (E i : ℂ) • bE i := by
    simpa [E, bE] using Hop.2.isSymmetric.apply_eigenvectorBasis rfl i
  let hPurePointSummable : PurePointGibbsSummable E β :=
    purePointGibbsSummable_of_finite E β
  have hPartition :
      purePointPartitionFunction E β = spectralTrace (gibbsOp Hop β) :=
    purePointPartitionFunction_eq_spectralTrace_gibbsOp
      Hop β hcompact hsummable bE.toHilbertBasis E (fun i => by simpa using hEbE i)
  have hPartitionPos : 0 < purePointPartitionFunction E β := by
    rw [hPartition]
    exact spectralTrace_gibbsOp_pos Hop β hZ
  have hρbE (i : Fin (Module.finrank ℂ H)) :
      (ρ.op : H →ₗ[ℂ] H) (bE i) =
        (purePointGibbsProbability E β i : ℂ) • bE i := by
    simpa [ρ, purePointGibbsProbability, purePointBoltzmannWeight, hPartition] using
      (gibbsState_apply_eigenvector Hop β hcompact hsummable hZ (hEbE i))
  have hEntropy := vonNeumannEntropy_gibbs_diagonal
    ρ Hop bE.toHilbertBasis E β hPurePointSummable hPartitionPos
    (fun i => by simpa using hρbE i) (fun i => by simpa using hEbE i)
    ρ.entropyOp_hasSummableRealEigenvalues
  change vonNeumannEntropy ρ ≠ ⊤ ∧
    (vonNeumannEntropy ρ).toReal =
      β * energyExpValue ρ Hop + Real.log (spectralTrace (gibbsOp Hop β))
  simpa [hPartition] using hEntropy

/-- The normalized Gibbs state attains the Helmholtz lower bound exactly. -/
theorem gibbsState_helmholtzFreeEnergy_eq (Hop : Observable H) (β : ℝ) (hβ : 0 < β)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β hcompact hsummable hZ)).toReal =
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β)) := by
  have hEntropy :=
    (vonNeumannEntropy_gibbsState Hop β hcompact hsummable hZ).2
  rw [hEntropy, mul_add]
  have hβne : β ≠ 0 := hβ.ne'
  have hscale :
      (1 / β) *
          (β * energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop) =
        energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hβne, one_mul]
  rw [hscale]
  ring

/-- Every density operator has Helmholtz free energy at least that of the normalized Gibbs state. -/
theorem gibbsState_minimizes_helmholtzFreeEnergy (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β hcompact hsummable hZ)).toReal ≤
      energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal := by
  rw [gibbsState_helmholtzFreeEnergy_eq Hop β hβ hcompact hsummable hZ]
  exact (helmholtzFreeEnergy_ge_and_entropy_ne_top
    ρ Hop β hβ hcompact hsummable hZ).2

end QuantumTheory
