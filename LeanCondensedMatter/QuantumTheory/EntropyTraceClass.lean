import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Von Neumann entropy via trace-class operators (infinite dimensions)

Extends the von Neumann entropy (`QuantumTheory.vonNeumannEntropy` in
`QuantumTheory/Entropy.lean`) beyond finite-dimensional `H`, computed from the eigenvalues of a
`QuantumTheory.TraceClass.DensityOperator` (`ContinuousLinearMap.EigenvectorIndex`) rather than a
finite `Fin n`-indexed eigenvalue list.

**This file is additive, not a replacement**: the finite-dimensional `QuantumTheory.Entropy` and
everything built on it are untouched.

**Scope note (a genuine mathematical fact, not a Lean technicality):** in finite dimensions
`vonNeumannEntropy` is a finite sum, so it is automatically real-valued and finite. In infinite
dimensions the analogous sum `-Σᵢ λᵢ ln λᵢ` ranges over a countably infinite family: even though
`Σᵢ λᵢ` converges (`ρ` is trace-class), the entropy sum `Σᵢ (-λᵢ ln λᵢ)` — despite every term
being nonnegative — can genuinely diverge (e.g. `λᵢ = c / (i log² i)` for suitable `c`, summable,
but `-λᵢ ln λᵢ ~ c / (i log i)`, not summable). This is a real physical phenomenon (a trace-class
density operator can have infinite von Neumann entropy), not an artifact of the formalization, so
`vonNeumannEntropy` below is `ENNReal`-valued (`[0, ∞]`) rather than `ℝ`-valued: the sum is always
well-defined, with divergence showing up honestly as `⊤` rather than being silently truncated to
the junk value `0` that a real-valued `tsum` would give.

The bounded operator `entropyOp ρ = -ρ log ρ` is separately available through continuous
functional calculus. Its existence and compactness need no finite-dimensionality or
entropy-summability hypothesis; only taking its spectral trace requires the transformed
eigenvalues to be summable.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The eigenvalues of a density operator are nonnegative** — they are the probabilities `p_i`
of measuring the system in the corresponding eigenstate, matching the finite-dimensional
`QuantumTheory.eigenvalues_nonneg`. -/
theorem eigenvalue_nonneg (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) : 0 ≤ a.1.1 :=
  eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a

/-- The bounded entropy operator obtained by applying `x ↦ -x log x` to a density operator.
Unlike its spectral trace, this operator exists without a finite-entropy assumption. -/
noncomputable def entropyOp (ρ : DensityOperator H) : H →L[ℂ] H :=
  cfc Real.negMulLog ρ.op

/-- The entropy operator acts on an eigenvector by applying `Real.negMulLog` to its eigenvalue. -/
theorem entropyOp_apply_eigenvector (ρ : DensityOperator H) {v : H} {c : ℝ}
    (hv : (ρ.op : H →ₗ[ℂ] H) v = (c : ℂ) • v) :
    entropyOp ρ v = (Real.negMulLog c : ℂ) • v := by
  simpa [entropyOp] using
    (cfc_apply_eigenvector (T := ρ.op) ρ.pos.isSelfAdjoint hv
      (f := Real.negMulLog) Real.continuous_negMulLog)

/-- The entropy operator of a trace-class density operator is compact. This follows because the
density operator is compact, `Real.negMulLog` is continuous, and `Real.negMulLog 0 = 0`. -/
theorem entropyOp_isCompact (ρ : DensityOperator H) :
    IsCompactOperator (entropyOp ρ : H →L[ℂ] H) := by
  rw [entropyOp]
  exact isCompactOperator_cfc_of_zero ρ.pos.isSelfAdjoint ρ.spectralTraceClass.compact
    Real.continuous_negMulLog (by simp)

/-- Bundle the entropy operator as a spectral-trace-class operator once absolute summability of its
nonzero real eigenvalues is supplied. Compactness and symmetry are derived automatically from the
density operator and continuous functional calculus. -/
def entropyOpSpectralTraceClass (ρ : DensityOperator H)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    SpectralTraceClass (entropyOp ρ) := by
  simpa [entropyOp] using
    (SpectralTraceClass.ofCFC (T := ρ.op) ρ.pos.isSelfAdjoint
      ρ.spectralTraceClass.compact Real.continuous_negMulLog (by simp)
      (by simpa [entropyOp] using hsummable))

/-- **The von Neumann entropy `-Tr[ρ ln ρ]` of a density operator (infinite-dimensional)**,
computed from `ρ`'s eigenvalues via `ContinuousLinearMap.EigenvectorIndex`. `ENNReal`-valued
(`[0, ∞]`), unlike the finite-dimensional `QuantumTheory.vonNeumannEntropy`: see the module
docstring above for why the entropy sum can genuinely diverge even for a trace-class `ρ`. -/
noncomputable def vonNeumannEntropy (ρ : DensityOperator H) : ENNReal :=
  ∑' a : EigenvectorIndex ρ.op, ENNReal.ofReal (Real.negMulLog a.1.1)

end QuantumTheory.TraceClass
