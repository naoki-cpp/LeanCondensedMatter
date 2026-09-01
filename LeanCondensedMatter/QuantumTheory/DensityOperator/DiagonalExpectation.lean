import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt.InnerProduct
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Countable diagonal expectation formulas

The positive square root of a density operator is Hilbert–Schmidt. This identifies the canonical
spectral expectation with the Hilbert–Schmidt pairing `⟪√ρ, A√ρ⟫`, whose basis independence yields
countable Hilbert-basis formulas and absolute convergence without a finite-dimensional hypothesis.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The positive square root of a density operator. -/
noncomputable def DensityOperator.sqrtOp (ρ : DensityOperator H) : H →L[ℂ] H :=
  cfc Real.sqrt ρ.op

/-- The square-root density operator acts on an eigenvector by the square root of its eigenvalue. -/
theorem DensityOperator.sqrtOp_apply_eigenvector (ρ : DensityOperator H) {v : H} {c : ℝ}
    (hv : (ρ.op : H →ₗ[ℂ] H) v = (c : ℂ) • v) :
    ρ.sqrtOp v = (Real.sqrt c : ℂ) • v := by
  simpa [DensityOperator.sqrtOp] using
    (cfc_apply_eigenvector (T := ρ.op) ρ.pos.isSelfAdjoint hv
      (f := Real.sqrt) Real.continuous_sqrt)

/-- The positive square root of a density operator is Hilbert–Schmidt. Its squared
Hilbert–Schmidt norm is the trace-one eigenvalue sum. -/
theorem DensityOperator.sqrtOp_isHilbertSchmidt (ρ : DensityOperator H) :
    IsHilbertSchmidt ρ.sqrtOp := by
  classical
  let hρcompact : IsCompactOperator ρ.op := ρ.spectralTraceClass.compact
  let hρsym : ρ.op.IsSymmetric := ρ.isSymmetric
  let e : EigenvectorIndex ρ.op → H := eigenvectorFamily hρcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hρcompact hρsym
  obtain ⟨u, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : EigenvectorIndex ρ.op → u := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a a' haa'
    apply he.linearIndependent.injective
    exact congrArg Subtype.val haa'
  let g : u → ℝ := fun i => ‖ρ.sqrtOp (b i)‖ ^ 2
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
  have hpoint (a : EigenvectorIndex ρ.op) : g (j a) = a.1.1 := by
    change ‖ρ.sqrtOp (b (j a))‖ ^ 2 = a.1.1
    rw [hb_j, ρ.sqrtOp_apply_eigenvector (apply_eigenvectorFamily hρcompact a),
      norm_smul, he.1 a]
    simp [Real.sq_sqrt (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)]
  have hzero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    have hxker := hilbertBasis_apply_eq_zero_of_not_mem_eigenvector_range
      hρcompact hρsym b j (fun a => by simpa [e] using hb_j a) x hx
    have hsqrt : ρ.sqrtOp (b x) = 0 := by
      simpa using ρ.sqrtOp_apply_eigenvector (v := b x) (c := 0) (by simpa using hxker)
    change ‖ρ.sqrtOp (b x)‖ ^ 2 = 0
    simp [hsqrt]
  have hweights : HasSum (fun a : EigenvectorIndex ρ.op => a.1.1) 1 := by
    have h := (summable_eigenvectorIndex ρ.spectralTraceClass.summable).hasSum
    have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
      simpa [spectralTrace] using ρ.spectralTrace_op_eq_one
    rwa [htrace] at h
  have hrestricted : HasSum (g ∘ j) 1 := by
    simpa only [Function.comp_apply] using
      HasSum.congr_fun hweights hpoint
  have hfull : HasSum g 1 := (hj.hasSum_iff hzero).mp hrestricted
  exact IsHilbertSchmidt.of_isHilbertSchmidtWrt hfull.summable

/-- The canonical density-state expectation is the basis-independent Hilbert–Schmidt pairing
`⟪√ρ, A√ρ⟫`. This formula is valid for every bounded operator, not only observables. -/
theorem DensityOperator.expectation_eq_innerHS (ρ : DensityOperator H)
    (A : H →L[ℂ] H) (d : HilbertBasis ι ℂ H) :
    ρ.expectation A = innerHS d ρ.sqrtOp (A * ρ.sqrtOp) := by
  classical
  let hsqrt : IsHilbertSchmidt ρ.sqrtOp := ρ.sqrtOp_isHilbertSchmidt
  let hAsqrt : IsHilbertSchmidt (A * ρ.sqrtOp) := isHilbertSchmidt_comp_left A hsqrt
  let hρcompact : IsCompactOperator ρ.op := ρ.spectralTraceClass.compact
  let hρsym : ρ.op.IsSymmetric := ρ.isSymmetric
  let e : EigenvectorIndex ρ.op → H := eigenvectorFamily hρcompact
  have he : Orthonormal ℂ e := by
    simpa [e] using orthonormal_eigenvectorFamily hρcompact hρsym
  obtain ⟨u, b, hsub, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : EigenvectorIndex ρ.op → u := fun a => ⟨e a, hsub ⟨a, rfl⟩⟩
  have hj : Function.Injective j := by
    intro a a' haa'
    apply he.linearIndependent.injective
    exact congrArg Subtype.val haa'
  let g : u → ℂ := fun i => inner ℂ (ρ.sqrtOp (b i)) ((A * ρ.sqrtOp) (b i))
  have hb_j (a : EigenvectorIndex ρ.op) : b (j a) = e a := by
    rw [hb]
  have hpoint (a : EigenvectorIndex ρ.op) :
      g (j a) = (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)) := by
    change inner ℂ (ρ.sqrtOp (b (j a))) ((A * ρ.sqrtOp) (b (j a))) = _
    rw [hb_j, ρ.sqrtOp_apply_eigenvector (apply_eigenvectorFamily hρcompact a),
      mul_apply_eq_comp, ρ.sqrtOp_apply_eigenvector (apply_eigenvectorFamily hρcompact a),
      map_smul, inner_smul_left, inner_smul_right]
    have hsqrt_sq_real :
        Real.sqrt a.1.1 * Real.sqrt a.1.1 = a.1.1 := by
      simpa [pow_two] using
        Real.sq_sqrt (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)
    have hsqrt_sq :
        (Real.sqrt a.1.1 : ℂ) * (Real.sqrt a.1.1 : ℂ) = (a.1.1 : ℂ) := by
      exact_mod_cast hsqrt_sq_real
    have hstar :
        starRingEnd ℂ (Real.sqrt a.1.1 : ℂ) = (Real.sqrt a.1.1 : ℂ) := by
      simp
    rw [hstar, ← mul_assoc, hsqrt_sq]
  have hzero (x : u) (hx : x ∉ Set.range j) : g x = 0 := by
    have hxker := hilbertBasis_apply_eq_zero_of_not_mem_eigenvector_range
      hρcompact hρsym b j (fun a => by simpa [e] using hb_j a) x hx
    have hsqrt_zero : ρ.sqrtOp (b x) = 0 := by
      simpa using ρ.sqrtOp_apply_eigenvector (v := b x) (c := 0) (by simpa using hxker)
    change inner ℂ (ρ.sqrtOp (b x)) ((A * ρ.sqrtOp) (b x)) = 0
    simp [hsqrt_zero]
  have hfull : HasSum g (innerHS b ρ.sqrtOp (A * ρ.sqrtOp)) := by
    change HasSum (fun i => inner ℂ (ρ.sqrtOp (b i)) ((A * ρ.sqrtOp) (b i)))
      (innerHS b ρ.sqrtOp (A * ρ.sqrtOp))
    exact (summable_inner_apply_of_isHilbertSchmidtWrt b
      (hsqrt.isHilbertSchmidtWrt b) (hAsqrt.isHilbertSchmidtWrt b)).hasSum
  have hrestricted : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)))
      (innerHS b ρ.sqrtOp (A * ρ.sqrtOp)) := by
    simpa only [Function.comp_apply] using
      HasSum.congr_fun ((hj.hasSum_iff hzero).mpr hfull) fun a => (hpoint a).symm
  have hexpect : HasSum
      (fun a : EigenvectorIndex ρ.op =>
        (a.1.1 : ℂ) * inner ℂ (e a) (A (e a)))
      (ρ.expectation A) := by
    rw [ρ.expectation_apply]
    exact (ρ.summable_expectation_term A).hasSum
  have hbasis : ρ.expectation A = innerHS b ρ.sqrtOp (A * ρ.sqrtOp) :=
    hexpect.unique hrestricted
  calc
    ρ.expectation A = innerHS b ρ.sqrtOp (A * ρ.sqrtOp) := hbasis
    _ = innerHS d ρ.sqrtOp (A * ρ.sqrtOp) :=
      (innerHS_eq_of_isHilbertSchmidt d b hsqrt hAsqrt).symm

end QuantumTheory
