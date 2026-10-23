import LeanCondensedMatter.QuantumTheory.Gibbs.Boltzmann
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula

/-!
# Gibbs states in an energy eigenbasis

Construct the Gibbs density operator on a Hilbert space from an energy eigenbasis and the
scalar Gibbs–Boltzmann data in `Gibbs.Boltzmann`. This also covers summable weights on
infinite-dimensional spaces without requiring a bounded Hamiltonian.
-/

noncomputable section

namespace QuantumTheory

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical pure-point Gibbs density operator.  No bounded Hamiltonian is introduced: the
state is built directly from the spectral Boltzmann weights. -/
noncomputable def eigenbasisGibbsDensityOperator [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) : DensityOperator H :=
  diagonalDensityOperator b (eigenbasisBoltzmannWeight E β) hsum
    (eigenbasisBoltzmannWeight_nonneg E β)
    (by simpa [eigenbasisPartitionFunction] using eigenbasisPartitionFunction_pos E β hsum)

/-- The pure-point Gibbs density operator acts diagonally with the normalized Boltzmann
probabilities. -/
@[simp]
theorem eigenbasisGibbsDensityOperator_apply_basis [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (i : ι) :
    (eigenbasisGibbsDensityOperator b E β hsum).op (b i) =
      (eigenbasisGibbsProbability E β i : ℂ) • b i := by
  have hZ : 0 < ∑' j, eigenbasisBoltzmannWeight E β j := by
    simpa [eigenbasisPartitionFunction] using eigenbasisPartitionFunction_pos E β hsum
  simpa [eigenbasisGibbsDensityOperator, eigenbasisGibbsProbability,
    eigenbasisPartitionFunction, Real.normalizedWeight] using
    diagonalDensityOperator_apply_basis b (eigenbasisBoltzmannWeight E β) hsum
      (eigenbasisBoltzmannWeight_nonneg E β) hZ i

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded linear map carrying one energy basis to another intertwines the Gibbs density
operators with the same energies and inverse temperature. -/
theorem eigenbasisGibbsDensityOperator_intertwines [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis ι ℂ K) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (F : H →L[ℂ] K)
    (hbasis : ∀ i, F (b i) = c i) :
    F.comp (eigenbasisGibbsDensityOperator b E β hsum).op =
      (eigenbasisGibbsDensityOperator c E β hsum).op.comp F := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i, rfl⟩
  simp only [ContinuousLinearMap.comp_apply, eigenbasisGibbsDensityOperator_apply_basis,
    map_smul, hbasis]

/-- A unitary change of energy basis preserves Gibbs expectations when the observable is
transported back by the inverse unitary. The energy labels and temperature are unchanged. -/
theorem eigenbasisGibbsDensityOperator_expectation_transport [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis ι ℂ K) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (e : H ≃ₗᵢ[ℂ] K)
    (hbasis : ∀ i, e (b i) = c i) (A : K →L[ℂ] K) :
    (eigenbasisGibbsDensityOperator c E β hsum).expectation A =
      (eigenbasisGibbsDensityOperator b E β hsum).expectation
        (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (A.comp e.toContinuousLinearEquiv.toContinuousLinearMap)) := by
  rw [(eigenbasisGibbsDensityOperator c E β hsum).expectation_eq_tsum_diagonal
    A c (eigenbasisGibbsProbability E β)
    (eigenbasisGibbsDensityOperator_apply_basis c E β hsum)]
  rw [(eigenbasisGibbsDensityOperator b E β hsum).expectation_eq_tsum_diagonal
    _ b (eigenbasisGibbsProbability E β)
    (eigenbasisGibbsDensityOperator_apply_basis b E β hsum)]
  apply tsum_congr
  intro i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [← hbasis i]
  have hinner := e.inner_map_map (b i) (e.symm (A (e (b i))))
  simpa only [e.apply_symm_apply] using
    congrArg (fun z : ℂ => (eigenbasisGibbsProbability E β i : ℂ) * z) hinner

end QuantumTheory
