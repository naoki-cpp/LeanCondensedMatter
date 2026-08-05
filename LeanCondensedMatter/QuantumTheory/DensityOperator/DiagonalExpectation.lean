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
    have hspan : Submodule.span ℂ (Set.range e) ≤ (ℂ ∙ (b x : H))ᗮ := by
      rw [Submodule.span_le]
      rintro y ⟨a, rfl⟩
      refine (Submodule.mem_orthogonal_singleton_iff_inner_left).2 ?_
      have hne : j a ≠ x := by
        intro h
        exact hx ⟨a, h⟩
      have horth : inner ℂ (b (j a)) (b x) = 0 := b.orthonormal.2 hne
      rw [hb_j] at horth
      exact horth
    have hxorth : (b x : H) ∈ (Submodule.span ℂ (Set.range e)).topologicalClosureᗮ := by
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
    have hfunctions : (g ∘ j) = fun a : EigenvectorIndex ρ.op => a.1.1 := by
      funext a
      exact hpoint a
    rw [hfunctions]
    exact hweights
  have hfull : HasSum g 1 := (hj.hasSum_iff hzero).mp hrestricted
  exact IsHilbertSchmidt.of_isHilbertSchmidtWrt hfull.summable

end QuantumTheory
