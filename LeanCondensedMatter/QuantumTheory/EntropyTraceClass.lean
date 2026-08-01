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

/-- Every eigenvalue of a density operator is at most one. This follows because all eigenvalues are
nonnegative and their spectral sum is one. -/
theorem density_eigenvalue_le_one (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    a.1.1 ≤ 1 := by
  have hs : Summable (fun b : EigenvectorIndex ρ.op => b.1.1) :=
    summable_eigenvectorIndex ρ.spectralTraceClass.summable
  calc
    a.1.1 = ∑ b ∈ ({a} : Finset (EigenvectorIndex ρ.op)), b.1.1 := by simp
    _ ≤ ∑' b : EigenvectorIndex ρ.op, b.1.1 :=
      Summable.sum_le_tsum {a} (fun b _ => eigenvalue_nonneg ρ b) hs
    _ = ρ.spectralTraceClass.trace := rfl
    _ = 1 := ρ.spectralTrace_eq_one

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

/-- The transformed density-operator eigenvalues `-λ log λ` sum to the spectral trace of the
entropy operator. The proof extends the density operator's orthonormal eigenvector family to a
Hilbert basis. Every added basis vector lies in `ker ρ`, so its entropy-operator diagonal
contribution vanishes. -/
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
  let g : w → ℝ := fun i => (inner ℂ (b i) (entropyOp ρ (b i)) : ℂ).re
  have hfull : HasSum g (entropyOpSpectralTraceClass ρ hsummable).trace :=
    (entropyOpSpectralTraceClass ρ hsummable).hasSum_inner_apply b
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
  have hpoint (a : EigenvectorIndex ρ.op) :
      g (j a) = Real.negMulLog a.1.1 := by
    change (inner ℂ (b (j a)) (entropyOp ρ (b (j a))) : ℂ).re =
      Real.negMulLog a.1.1
    rw [hb_j]
    rw [entropyOp_apply_eigenvector ρ (apply_eigenvectorFamily hρcompact a)]
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      (orthonormal_eigenvectorFamily hρcompact hρsym).1 a]
    simp
  have hzero (x : w) (hx : x ∉ Set.range j) : g x = 0 := by
    have hspan :
        Submodule.span ℂ (Set.range e) ≤ (ℂ ∙ (b x : H))ᗮ := by
      rw [Submodule.span_le]
      rintro y ⟨a, rfl⟩
      refine (Submodule.mem_orthogonal_singleton_iff_inner_left).2 ?_
      have hne : j a ≠ x := by
        intro h
        exact hx ⟨a, h⟩
      have horth : inner ℂ (b (j a)) (b x) = 0 := b.orthonormal.2 hne
      rw [hb_j] at horth
      exact horth
    have hxorth :
        (b x : H) ∈ (Submodule.span ℂ (Set.range e)).topologicalClosureᗮ := by
      rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
      intro y hy
      have hy' := hspan hy
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1 hy'
    have hxker_mem :
        (b x : H) ∈ Module.End.eigenspace (ρ.op : H →ₗ[ℂ] H) (0 : ℂ) := by
      rw [← orthogonal_closure_span_eigenvectorFamily hρcompact hρsym]
      simpa [e] using hxorth
    have hxker : (ρ.op : H →ₗ[ℂ] H) (b x) = 0 := by
      have hxev := Module.End.mem_eigenspace_iff.mp hxker_mem
      simpa using hxev
    have hentropy : entropyOp ρ (b x) = 0 := by
      simpa using
        (entropyOp_apply_eigenvector ρ (v := b x) (c := 0) (by simpa using hxker))
    simp [g, hentropy]
  have hrestricted :
      HasSum (g ∘ j) (entropyOpSpectralTraceClass ρ hsummable).trace :=
    (hj.hasSum_iff hzero).mpr hfull
  have hfunctions :
      (g ∘ j) = fun a : EigenvectorIndex ρ.op => Real.negMulLog a.1.1 := by
    funext a
    exact hpoint a
  rwa [hfunctions] at hrestricted

/-- The spectral trace of the entropy operator is the sum of `-λ log λ` over the density
operator's nonzero eigenvalues. -/
theorem entropyOp_trace_eq_tsum (ρ : DensityOperator H)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    (entropyOpSpectralTraceClass ρ hsummable).trace =
      ∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1 :=
  (hasSum_negMulLog_eigenvalues ρ hsummable).tsum_eq.symm

/-- **The von Neumann entropy `-Tr[ρ ln ρ]` of a density operator (infinite-dimensional)**,
computed from `ρ`'s eigenvalues via `ContinuousLinearMap.EigenvectorIndex`. `ENNReal`-valued
(`[0, ∞]`), unlike the finite-dimensional `QuantumTheory.vonNeumannEntropy`: see the module
docstring above for why the entropy sum can genuinely diverge even for a trace-class `ρ`. -/
noncomputable def vonNeumannEntropy (ρ : DensityOperator H) : ENNReal :=
  ∑' a : EigenvectorIndex ρ.op, ENNReal.ofReal (Real.negMulLog a.1.1)

/-- Under the finite-entropy summability hypothesis, the `ENNReal`-valued von Neumann entropy is
the nonnegative-real embedding of the entropy operator's spectral trace. -/
theorem vonNeumannEntropy_eq_ofReal_entropyOp_trace (ρ : DensityOperator H)
    (hsummable : HasSummableRealEigenvalues (entropyOp ρ)) :
    vonNeumannEntropy ρ =
      ENNReal.ofReal (entropyOpSpectralTraceClass ρ hsummable).trace := by
  rw [vonNeumannEntropy]
  symm
  rw [entropyOp_trace_eq_tsum ρ hsummable]
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun a => Real.negMulLog_nonneg (eigenvalue_nonneg ρ a) (density_eigenvalue_le_one ρ a))
    (hasSum_negMulLog_eigenvalues ρ hsummable).summable

end QuantumTheory.TraceClass
