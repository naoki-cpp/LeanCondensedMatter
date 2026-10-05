import LeanCondensedMatter.QuantumTheory.DensityOperator.Normalize
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

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
theorem hasSum_purePointBoltzmannWeight_of_basis_action
    (K : H →L[ℂ] H) (htrace : IsTraceClass K)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    HasSum (fun i => (purePointBoltzmannWeight E β i : ℂ)) htrace.trace := by
  have hsum := htrace.hasSum_trace b
  exact HasSum.congr_fun hsum fun i => by
    rw [happly i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp

/-- For heat data diagonalized by the Boltzmann weights, trace-classness is exactly
finiteness of the pure-point partition sum. -/
theorem isTraceClass_iff_purePointGibbsSummable_of_basis_action
    (K : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    IsTraceClass K ↔ PurePointGibbsSummable E β := by
  constructor
  · intro htrace
    have hweights :=
      hasSum_purePointBoltzmannWeight_of_basis_action K htrace b E β happly
    have hnorm : Summable (fun i => ‖(purePointBoltzmannWeight E β i : ℂ)‖) :=
      hweights.summable.norm
    change Summable fun i => ‖purePointBoltzmannWeight E β i‖
    simpa [Complex.norm_real, Real.norm_eq_abs] using hnorm
  · intro hsum
    have hcomplex : Summable (fun i => ‖(purePointBoltzmannWeight E β i : ℂ)‖) := by
      simpa using hsum
    have hK :
        K = HilbertBasis.diagonalOp b
          (fun i => (purePointBoltzmannWeight E β i : ℂ)) := by
      apply ContinuousLinearMap.ext_on
        (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
      rintro _ ⟨i, rfl⟩
      rw [happly i,
        HilbertBasis.diagonalOp_apply_basis b
          (fun i => (purePointBoltzmannWeight E β i : ℂ)) hcomplex i]
    rw [hK]
    exact HilbertBasis.diagonalOp_isTraceClass b (purePointBoltzmannWeight E β) hsum
      (purePointBoltzmannWeight_nonneg E β)

/-- If supplied trace-class heat data act diagonally by the Boltzmann weights, their canonical
complex trace is the pure-point partition function embedded in `ℂ`. -/
theorem heatTrace_eq_purePointPartitionFunction_of_basis_action
    (K : H →L[ℂ] H) (htrace : IsTraceClass K)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    htrace.trace = (purePointPartitionFunction E β : ℂ) := by
  calc
    htrace.trace = ∑' i, (purePointBoltzmannWeight E β i : ℂ) :=
      (hasSum_purePointBoltzmannWeight_of_basis_action K htrace b E β happly).tsum_eq.symm
    _ = (purePointPartitionFunction E β : ℂ) := by
      rw [purePointPartitionFunction, Complex.ofReal_tsum]

/-- A positive nonzero trace-class heat operator with pure-point Boltzmann basis action normalizes
to the existing pure-point Gibbs density operator. -/
theorem DensityOperator.normalizePositive_eq_purePointGibbsDensityOperator_of_basis_action
    [Nonempty ι] (K : H →L[ℂ] H) (hpos : K.IsPositive)
    (htrace : IsTraceClass K) (hne : K ≠ 0)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (happly : ∀ i, K (b i) = (purePointBoltzmannWeight E β i : ℂ) • b i) :
    DensityOperator.normalizePositive K hpos htrace hne =
      purePointGibbsDensityOperator b E β
        ((isTraceClass_iff_purePointGibbsSummable_of_basis_action K b E β happly).mp htrace) := by
  let hsum :=
    (isTraceClass_iff_purePointGibbsSummable_of_basis_action K b E β happly).mp htrace
  have hpartition :
      spectralTrace K = purePointPartitionFunction E β := by
    apply Complex.ofReal_injective
    calc
      (spectralTrace K : ℂ) = htrace.trace :=
        (htrace.trace_eq_spectralTrace hpos.isSelfAdjoint).symm
      _ = (purePointPartitionFunction E β : ℂ) :=
        heatTrace_eq_purePointPartitionFunction_of_basis_action K htrace b E β happly
  change DensityOperator.normalizePositive K hpos htrace hne =
    purePointGibbsDensityOperator b E β hsum
  apply DensityOperator.ext
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨i, rfl⟩
  rw [DensityOperator.normalizePositive_op, smul_apply, happly i,
    purePointGibbsDensityOperator_apply_basis]
  rw [hpartition]
  rw [purePointGibbsProbability]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  apply congrArg (fun z : ℂ => z • b i)
  push_cast
  rfl

end QuantumTheory
