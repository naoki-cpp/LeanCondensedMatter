import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

/-!
# Heat-operator compatibility with pure-point Gibbs states

A bounded heat operator is accepted as operator data rather than wrapped in a second Gibbs-state
structure. When it acts on a Hilbert basis by the Boltzmann factors, its general trace and canonical
positive normalization agree with the existing pure-point Gibbs construction.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If supplied trace-class heat data act diagonally by the Boltzmann weights, those weights sum to
the canonical complex trace. -/
theorem hasSum_eigenbasisBoltzmannWeight_of_basis_action
    (K : H →L[ℂ] H) (htrace : IsTraceClass K)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (eigenbasisBoltzmannWeight E β i : ℂ) • b i) :
    HasSum (fun i => (eigenbasisBoltzmannWeight E β i : ℂ)) htrace.trace := by
  have hsum := htrace.hasSum_trace b
  exact HasSum.congr_fun hsum fun i => by
    rw [happly i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp

/-- For heat data diagonalized by the Boltzmann weights, trace-classness is exactly
finiteness of the pure-point partition sum. -/
theorem isTraceClass_iff_eigenbasisGibbsSummable_of_basis_action
    (K : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (eigenbasisBoltzmannWeight E β i : ℂ) • b i) :
    IsTraceClass K ↔ EigenbasisGibbsSummable E β := by
  constructor
  · intro htrace
    have hweights :=
      hasSum_eigenbasisBoltzmannWeight_of_basis_action K htrace b E β happly
    have hnorm : Summable (fun i => ‖(eigenbasisBoltzmannWeight E β i : ℂ)‖) :=
      hweights.summable.norm
    change Summable fun i => ‖eigenbasisBoltzmannWeight E β i‖
    simpa [Complex.norm_real, Real.norm_eq_abs] using hnorm
  · intro hsum
    change Summable (fun i => ‖eigenbasisBoltzmannWeight E β i‖) at hsum
    have hcomplex : Summable (fun i => ‖(eigenbasisBoltzmannWeight E β i : ℂ)‖) := by
      simpa using hsum
    have hK :
        K = HilbertBasis.diagonalOp b
          (fun i => (eigenbasisBoltzmannWeight E β i : ℂ)) := by
      apply ContinuousLinearMap.ext_on
        (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
      rintro _ ⟨i, rfl⟩
      rw [happly i,
        HilbertBasis.diagonalOp_apply_basis b
          (fun i => (eigenbasisBoltzmannWeight E β i : ℂ)) hcomplex i]
    rw [hK]
    exact HilbertBasis.diagonalOp_isTraceClass b (eigenbasisBoltzmannWeight E β) hsum
      (eigenbasisBoltzmannWeight_nonneg E β)

/-- If supplied trace-class heat data act diagonally by the Boltzmann weights, their canonical
complex trace is the pure-point partition function embedded in `ℂ`. -/
theorem heatTrace_eq_eigenbasisPartitionFunction_of_basis_action
    (K : H →L[ℂ] H) (htrace : IsTraceClass K)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (eigenbasisBoltzmannWeight E β i : ℂ) • b i) :
    htrace.trace = (eigenbasisPartitionFunction E β : ℂ) := by
  calc
    htrace.trace = ∑' i, (eigenbasisBoltzmannWeight E β i : ℂ) :=
      (hasSum_eigenbasisBoltzmannWeight_of_basis_action K htrace b E β happly).tsum_eq.symm
    _ = (eigenbasisPartitionFunction E β : ℂ) := by
      rw [eigenbasisPartitionFunction, Complex.ofReal_tsum]

/-- Pure-point Boltzmann heat data normalize directly to the canonical Gibbs density
operator at the operator level. -/
theorem inv_partition_smul_heat_eq_eigenbasisGibbsDensityOperator_op
    [Nonempty ι] (K : H →L[ℂ] H)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β)
    (happly : ∀ i, K (b i) = (eigenbasisBoltzmannWeight E β i : ℂ) • b i) :
    ((eigenbasisPartitionFunction E β)⁻¹ : ℂ) • K =
      (eigenbasisGibbsDensityOperator b E β hsum).op := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i, rfl⟩
  rw [smul_apply, happly i, eigenbasisGibbsDensityOperator_apply_basis,
    eigenbasisGibbsProbability, smul_smul]
  apply congrArg (fun z : ℂ => z • b i)
  push_cast
  rfl

end QuantumTheory
