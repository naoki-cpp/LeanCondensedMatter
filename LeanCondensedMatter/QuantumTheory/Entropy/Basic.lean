import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Von Neumann entropy

The canonical entropy is `ENNReal`-valued because a density operator can have infinite entropy even
when it is trace-class. The bounded entropy operator `-ρ log ρ` is also provided; taking its spectral
trace requires an additional summability hypothesis.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded entropy operator obtained by applying `x ↦ -x log x` to a density operator. -/
noncomputable def entropyOp (ρ : DensityOperator H) : H →L[ℂ] H :=
  cfc Real.negMulLog ρ.op

/-- The entropy operator acts on an eigenvector by applying `Real.negMulLog` to its eigenvalue. -/
theorem entropyOp_apply_eigenvector (ρ : DensityOperator H) {v : H} {c : ℝ}
    (hv : (ρ.op : H →ₗ[ℂ] H) v = (c : ℂ) • v) :
    entropyOp ρ v = (Real.negMulLog c : ℂ) • v := by
  simpa [entropyOp] using
    (cfc_apply_eigenvector (T := ρ.op) ρ.pos.isSelfAdjoint hv
      (f := Real.negMulLog) Real.continuous_negMulLog)

/-- The entropy operator of a density operator is compact. -/
theorem entropyOp_isCompact (ρ : DensityOperator H) :
    IsCompactOperator (entropyOp ρ : H →L[ℂ] H) := by
  rw [entropyOp]
  exact isCompactOperator_cfc_of_zero ρ.pos.isSelfAdjoint ρ.spectralTraceClass.compact
    Real.continuous_negMulLog (by simp)

/-- Bundle the entropy operator as spectral-trace-class once summability is supplied. -/
theorem entropyOpSpectralTraceClass (ρ : DensityOperator H)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    SpectralTraceClass (entropyOp ρ) := by
  simpa [entropyOp] using
    (SpectralTraceClass.ofCFC (T := ρ.op) ρ.pos.isSelfAdjoint
      ρ.spectralTraceClass.compact Real.continuous_negMulLog (by simp)
      (by simpa [entropyOp] using hsummable))

/-- The transformed eigenvalues sum to the spectral trace of the entropy operator. -/
theorem hasSum_negMulLog_eigenvalues (ρ : DensityOperator H)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    HasSum (fun a : EigenvectorIndex ρ.op => Real.negMulLog a.1.1)
      (entropyOpSpectralTraceClass ρ hsummable).trace := by
  classical
  let hρcompact : IsCompactOperator ρ.op := ρ.spectralTraceClass.compact
  let hρsym : ρ.op.IsSymmetric := ρ.pos.isSelfAdjoint.isSymmetric
  let e : EigenvectorIndex ρ.op → H := eigenvectorFamily hρcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hρcompact hρsym
  obtain ⟨w, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : EigenvectorIndex ρ.op → w := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a a' haa'
    apply he.linearIndependent.injective
    exact congrArg Subtype.val haa'
  let g : w → ℝ := fun i =>
    diagonalExpectationValue (entropyOp ρ)
      (entropyOpSpectralTraceClass ρ hsummable).isSelfAdjoint (b i)
  have hfull : HasSum g (entropyOpSpectralTraceClass ρ hsummable).trace := by
    simpa [g] using
      (entropyOpSpectralTraceClass ρ hsummable).hasSum_diagonalExpectationValue b
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
  have hpoint (a : EigenvectorIndex ρ.op) :
      g (j a) = Real.negMulLog a.1.1 := by
    change diagonalExpectationValue (entropyOp ρ)
      (entropyOpSpectralTraceClass ρ hsummable).isSelfAdjoint (b (j a)) =
        Real.negMulLog a.1.1
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hb_j]
    rw [entropyOp_apply_eigenvector ρ (apply_eigenvectorFamily hρcompact a)]
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      (orthonormal_eigenvectorFamily hρcompact hρsym).1 a]
    simp
  have hzero (x : w) (hx : x ∉ Set.range j) : g x = 0 := by
    have hxker := hilbertBasis_apply_eq_zero_of_not_mem_eigenvector_range
      hρcompact hρsym b j (fun a => by simpa [e] using hb_j a) x hx
    have hentropy : entropyOp ρ (b x) = 0 := by
      simpa using
        (entropyOp_apply_eigenvector ρ (v := b x) (c := 0) (by simpa using hxker))
    change diagonalExpectationValue (entropyOp ρ)
      (entropyOpSpectralTraceClass ρ hsummable).isSelfAdjoint (b x) = 0
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hentropy]
    simp
  have hrestricted :
      HasSum (g ∘ j) (entropyOpSpectralTraceClass ρ hsummable).trace :=
    (hj.hasSum_iff hzero).mpr hfull
  simpa only [Function.comp_apply] using
    HasSum.congr_fun hrestricted fun a => (hpoint a).symm

/-- The entropy-operator trace is the sum of `-λ log λ`. -/
theorem entropyOp_trace_eq_tsum (ρ : DensityOperator H)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    (entropyOpSpectralTraceClass ρ hsummable).trace =
      ∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1 :=
  (hasSum_negMulLog_eigenvalues ρ hsummable).tsum_eq.symm

/-- The von Neumann entropy of a density operator, allowing the value `∞`. -/
noncomputable def vonNeumannEntropy (ρ : DensityOperator H) : ENNReal :=
  ∑' a : EigenvectorIndex ρ.op, ENNReal.ofReal (Real.negMulLog a.1.1)

/-- Entropy is finite with real value the entropy `tsum` whenever that sum converges. -/
theorem vonNeumannEntropy_ne_top_and_toReal_eq_tsum (ρ : DensityOperator H)
    (hsum : Summable (fun a : EigenvectorIndex ρ.op => Real.negMulLog a.1.1)) :
    vonNeumannEntropy ρ ≠ ⊤ ∧
      (vonNeumannEntropy ρ).toReal = ∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1 := by
  have hnonneg : ∀ a : EigenvectorIndex ρ.op, 0 ≤ Real.negMulLog a.1.1 :=
    fun a => Real.negMulLog_nonneg (ρ.eigenvalue_nonneg a) (ρ.eigenvalue_le_one a)
  have hEntropyEq : vonNeumannEntropy ρ =
      ENNReal.ofReal (∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1) :=
    (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum).symm
  refine ⟨by rw [hEntropyEq]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hEntropyEq, ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]

/-- Under finite-entropy summability, entropy is the embedding of the entropy-operator trace. -/
theorem vonNeumannEntropy_eq_ofReal_entropyOp_trace (ρ : DensityOperator H)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    vonNeumannEntropy ρ =
      ENNReal.ofReal (entropyOpSpectralTraceClass ρ hsummable).trace := by
  rw [vonNeumannEntropy]
  symm
  rw [entropyOp_trace_eq_tsum ρ hsummable]
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun a => Real.negMulLog_nonneg (ρ.eigenvalue_nonneg a) (ρ.eigenvalue_le_one a))
    (hasSum_negMulLog_eigenvalues ρ hsummable).summable

end QuantumTheory
