import LeanCondensedMatter.QuantumTheory.DensityOperator.Normalize
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

/-!
# Heat-operator compatibility with pure-point Gibbs states

A bounded heat operator is accepted as operator data rather than wrapped in a second Gibbs-state
structure. When it acts on a Hilbert basis by the Boltzmann factors, its bundled spectral trace and
canonical positive normalization agree with the existing pure-point Gibbs construction.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If supplied heat data act diagonally by the Boltzmann weights, those weights sum to the
bundled spectral trace. -/
theorem hasSum_purePointBoltzmannWeight_of_basis_action
    (K : H →L[ℂ] H) (htrace : SpectralTraceClass K)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    HasSum (purePointBoltzmannWeight E β) htrace.trace := by
  have hsum := htrace.hasSum_diagonalExpectationValue b
  exact HasSum.congr_fun hsum fun i => by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, happly i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp

/-- Pure-point Boltzmann summability follows from spectral-trace-class heat data with the matching
basis action. -/
theorem purePointGibbsSummable_of_basis_action
    (K : H →L[ℂ] H) (htrace : SpectralTraceClass K)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    PurePointGibbsSummable E β := by
  have hweights :=
    hasSum_purePointBoltzmannWeight_of_basis_action K htrace b E β happly
  have habs : Summable fun i => |purePointBoltzmannWeight E β i| :=
    hweights.summable.congr fun i => by
      rw [abs_of_nonneg (purePointBoltzmannWeight_nonneg E β i)]
  simpa only [Real.norm_eq_abs] using habs

/-- If supplied heat data act diagonally by the Boltzmann weights, their bundled spectral trace is
the pure-point partition function. -/
theorem heatSpectralTrace_eq_purePointPartitionFunction_of_basis_action
    (K : H →L[ℂ] H) (htrace : SpectralTraceClass K)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    htrace.trace = purePointPartitionFunction E β := by
  rw [purePointPartitionFunction]
  exact (hasSum_purePointBoltzmannWeight_of_basis_action K htrace b E β happly).tsum_eq.symm

/-- A positive nonzero spectral-trace-class heat operator with pure-point Boltzmann basis action
normalizes to the existing pure-point Gibbs density operator. -/
theorem DensityOperator.normalizePositive_eq_purePointGibbsDensityOperator_of_basis_action
    [Nonempty ι] (K : H →L[ℂ] H) (hpos : K.IsPositive)
    (htrace : SpectralTraceClass K) (hne : K ≠ 0)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    DensityOperator.normalizePositive K hpos htrace hne =
      purePointGibbsDensityOperator b E β
        (purePointGibbsSummable_of_basis_action K htrace b E β happly) := by
  let hsum := purePointGibbsSummable_of_basis_action K htrace b E β happly
  change DensityOperator.normalizePositive K hpos htrace hne =
    purePointGibbsDensityOperator b E β hsum
  apply DensityOperator.ext
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i, rfl⟩
  rw [DensityOperator.normalizePositive_op, smul_apply, happly i,
    purePointGibbsDensityOperator_apply_basis]
  rw [heatSpectralTrace_eq_purePointPartitionFunction_of_basis_action K htrace b E β happly]
  rw [purePointGibbsProbability]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  apply congrArg (fun z : ℂ => z • b i)
  push_cast
  rfl

end QuantumTheory
