import LeanCondensedMatter.QuantumTheory.HelmholtzFreeEnergyTraceClass
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Gibbs-state entropy equality via trace-class operators

This file develops the equality case of the trace-class Helmholtz free-energy inequality for the
normalized Gibbs state. Under the current bounded-Hamiltonian API, compactness of the Gibbs
operator forces the ambient Hilbert space to be finite-dimensional; that fact is used only to
discharge summability of the Gibbs state's entropy operator.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normalized Gibbs state acts diagonally on every energy eigenvector. -/
theorem gibbsState_apply_eigenvector (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace hsummable ≠ 0) {v : H} {E : ℝ}
    (hv : (Hop.1 : H →ₗ[ℂ] H) v = (E : ℂ) • v) :
    (gibbsState Hop β hcompact hsummable hZ).op v =
      (((spectralTrace hsummable)⁻¹ : ℝ) • (Real.exp (-β * E) : ℂ)) • v := by
  change ((spectralTrace hsummable)⁻¹ • gibbsOp Hop β) v = _
  rw [smul_apply, gibbsOp_apply_eigenvector Hop β hv]

/-- In finite dimensions, the trace-class energy expectation agrees with the usual real part of
`Tr(ρ H)`. The proof extends the nonzero eigenvectors of `ρ` to an orthonormal basis; the added
basis vectors lie in `ker ρ`, so their diagonal contributions vanish. -/
theorem energyExpValue_eq_re_linearMap_trace [FiniteDimensional ℂ H]
    (ρ : DensityOperator H) (Hop : Observable H) :
    energyExpValue ρ Hop =
      (LinearMap.trace ℂ H ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H)).re := by
  classical
  let hρcompact : IsCompactOperator ρ.op := ρ.spectralTraceClass.compact
  let hρsym : ρ.op.IsSymmetric := ρ.isSymmetric
  let e : EigenvectorIndex ρ.op → H := eigenvectorFamily hρcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hρcompact hρsym
  obtain ⟨u, b, hsub, hb⟩ := he.toSubtypeRange.exists_orthonormalBasis_extension
  let j : EigenvectorIndex ρ.op → u := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a a' haa'
    apply he.linearIndependent.injective
    exact congrArg Subtype.val haa'
  let g : u → ℂ := fun i => inner ℂ (b i) ((ρ.op ∘L Hop.1) (b i))
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
  have hpoint (a : EigenvectorIndex ρ.op) :
      g (j a) = (a.1.1 : ℂ) * inner ℂ (e a) (Hop.1 (e a)) := by
    change inner ℂ (b (j a))
        ((ρ.op : H →ₗ[ℂ] H) ((Hop.1 : H →ₗ[ℂ] H) (b (j a)))) =
      (a.1.1 : ℂ) * inner ℂ (e a) ((Hop.1 : H →ₗ[ℂ] H) (e a))
    rw [hb_j]
    calc
      inner ℂ (e a)
          ((ρ.op : H →ₗ[ℂ] H) ((Hop.1 : H →ₗ[ℂ] H) (e a))) =
          inner ℂ ((ρ.op : H →ₗ[ℂ] H) (e a))
            ((Hop.1 : H →ₗ[ℂ] H) (e a)) :=
        (hρsym (e a) ((Hop.1 : H →ₗ[ℂ] H) (e a))).symm
      _ = (a.1.1 : ℂ) * inner ℂ (e a) ((Hop.1 : H →ₗ[ℂ] H) (e a)) := by
        rw [apply_eigenvectorFamily hρcompact, inner_smul_left]
        simp [e]
  have hzero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
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
    change inner ℂ (b x)
      ((ρ.op : H →ₗ[ℂ] H) ((Hop.1 : H →ₗ[ℂ] H) (b x))) = 0
    calc
      inner ℂ (b x)
          ((ρ.op : H →ₗ[ℂ] H) ((Hop.1 : H →ₗ[ℂ] H) (b x))) =
          inner ℂ ((ρ.op : H →ₗ[ℂ] H) (b x))
            ((Hop.1 : H →ₗ[ℂ] H) (b x)) :=
        (hρsym (b x) ((Hop.1 : H →ₗ[ℂ] H) (b x))).symm
      _ = 0 := by rw [hxker, inner_zero_left]
  have hfull : HasSum g (∑ i, g i) := hasSum_fintype _
  have hrestricted : HasSum (g ∘ j) (∑ i, g i) :=
    (hj.hasSum_iff hzero).mpr hfull
  have hfunctions :
      (g ∘ j) = fun a : EigenvectorIndex ρ.op =>
        (a.1.1 : ℂ) * inner ℂ (e a) (Hop.1 (e a)) := by
    funext a
    exact hpoint a
  rw [hfunctions] at hrestricted
  have hsum :
      (∑' a : EigenvectorIndex ρ.op,
        (a.1.1 : ℂ) * inner ℂ (e a) (Hop.1 (e a))) = ∑ i, g i :=
    (summable_energyExpValue_term ρ Hop).hasSum.unique hrestricted
  have htrace := LinearMap.trace_eq_sum_inner
    ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) b
  have hgtrace :
      LinearMap.trace ℂ H ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) =
        ∑ i, g i := by
    simpa [g] using htrace
  change (∑' a : EigenvectorIndex ρ.op,
    (a.1.1 : ℂ) * inner ℂ (e a) (Hop.1 (e a))).re = _
  rw [hsum, ← hgtrace]

/-- The entropy operator of the normalized Gibbs state has summable nonzero real eigenvalues.
For the current bounded notion of Hamiltonian this follows from compactness of the Gibbs operator,
which forces `H` to be finite-dimensional. -/
theorem gibbsState_entropyOp_hasSummableRealEigenvalues (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace hsummable ≠ 0) :
    HasSummableRealEigenvalues (entropyOp (gibbsState Hop β hcompact hsummable hZ)) := by
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  let ρ := gibbsState Hop β hcompact hsummable hZ
  have hEntropyCompact : IsCompactOperator (entropyOp ρ) := entropyOp_isCompact ρ
  have hEntropySelfAdjoint : IsSelfAdjoint (entropyOp ρ) := by
    rw [entropyOp]
    exact cfc_predicate _ _
  letI : Finite (EigenvectorIndex (entropyOp ρ)) :=
    (orthonormal_eigenvectorFamily hEntropyCompact hEntropySelfAdjoint.isSymmetric).linearIndependent.finite
  exact Summable.of_finite

end QuantumTheory.TraceClass
