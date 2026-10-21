import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator
import LeanCondensedMatter.QuantumTheory.Gibbs.EigenbasisEntropy
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy

/-!
# Gibbs-state variational equality

The normalized Gibbs state attains the Helmholtz lower bound. The bounded-Hamiltonian state is
identified with the canonical energy-eigenbasis Gibbs state, whose entropy identity supplies
the finite-dimensional result.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gibbs state has finite entropy and satisfies `S(ρβ) = β E(ρβ) + log Z`. -/
theorem vonNeumannEntropy_gibbsState [Nontrivial H] [FiniteDimensional ℂ H]
    (Hop : Observable H) (β : ℝ) :
    vonNeumannEntropy (gibbsState Hop β) ≠ ⊤ ∧
      (vonNeumannEntropy (gibbsState Hop β)).toReal =
        β * energyExpValue (gibbsState Hop β) Hop +
          Real.log (spectralTrace (gibbsOp Hop β)) := by
  classical
  let E : Fin (Module.finrank ℂ H) → ℝ :=
    Hop.2.isSymmetric.eigenvalues rfl
  let bE : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    Hop.2.isSymmetric.eigenvectorBasis rfl
  have hEbE (i : Fin (Module.finrank ℂ H)) :
      Hop.1 (bE.toHilbertBasis i) = (E i : ℂ) • bE.toHilbertBasis i := by
    simp only [OrthonormalBasis.coe_toHilbertBasis]
    change (Hop.1 : H →ₗ[ℂ] H) (bE i) = (E i : ℂ) • bE i
    exact Hop.2.isSymmetric.apply_eigenvectorBasis rfl i
  letI : Nonempty (Fin (Module.finrank ℂ H)) :=
    ⟨⟨0, Module.finrank_pos (R := ℂ) (M := H)⟩⟩
  let hsum := eigenbasisGibbsSummable_of_finite E β
  simp only [gibbsState_eq_eigenbasisGibbsDensityOperator Hop β bE.toHilbertBasis E hsum hEbE,
    spectralTrace_gibbsOp_eq_eigenbasisPartitionFunction Hop β bE.toHilbertBasis E hEbE]
  have h := vonNeumannEntropy_eigenbasisGibbsDensityOperator bE.toHilbertBasis E β hsum
    (by exact Summable.of_finite)
  rw [eigenbasisGibbsEnergyExpectation_eq_energyExpValue
    bE.toHilbertBasis E β hsum Hop hEbE] at h
  exact h

/-- For nonzero inverse temperature, the normalized Gibbs state satisfies the exact Helmholtz
free-energy identity. -/
theorem gibbsState_helmholtzFreeEnergy_eq [Nontrivial H] [FiniteDimensional ℂ H]
    (Hop : Observable H) (β : ℝ) (hβ : β ≠ 0) :
    energyExpValue (gibbsState Hop β) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β)).toReal =
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β)) := by
  rw [(vonNeumannEntropy_gibbsState Hop β).2]
  field_simp [hβ]
  ring

/-- Every density operator has Helmholtz free energy at least that of the normalized Gibbs state. -/
theorem gibbsState_minimizes_helmholtzFreeEnergy [Nontrivial H] [FiniteDimensional ℂ H]
    (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) :
    energyExpValue (gibbsState Hop β) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β)).toReal ≤
      energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal := by
  rw [gibbsState_helmholtzFreeEnergy_eq Hop β hβ.ne']
  exact (helmholtzFreeEnergy_ge_and_entropy_ne_top
    ρ Hop β hβ).2

end QuantumTheory
