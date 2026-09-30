import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Vector
import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Observable

set_option linter.style.header false

/-!
# Axiomatic quantum theory: minimal postulates

Minimal formalization of the standard (Dirac–von Neumann) axiomatic quantum theory:
the state-vector representation postulate and the project-facing names for bounded observables and
vector-state expectations.

The general observable and vector-state infrastructure is reused from
`PhyslibAlpha.ProbabilisticTheory`.

See `notes/model-and-assumptions.md` for the physics-to-Lean correspondence and
scope notes.
-/

namespace QuantumTheory

/-- **State space postulate.** A pure state of a quantum system has a unit-vector representative in
a complex Hilbert space `H`. `StateVector H` stores the representative rather than identifying
vectors that differ by global phase. -/
def StateVector (H : Type*) [NormedAddCommGroup H] :=
  { ψ : H // ‖ψ‖ = 1 }

/-- A bounded observable is a self-adjoint bounded linear operator on the state space.

This is the Hilbert-space specialization of PhyslibAlpha's general observable type. -/
abbrev Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  _root_.Observable (H →L[ℂ] H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : Observable H) (ψ : StateVector H)

/-- The canonical complex expectation of an observable `A` in a state-vector representative `ψ`,
implemented by PhyslibAlpha's vector state. -/
noncomputable def expValue : ℂ :=
  UnitalPositiveLinearMap.ofVec ψ.2 A.1

/-- The canonical real observable expectation of a normalized vector representative. -/
noncomputable def observableExpValue : ℝ :=
  (UnitalPositiveLinearMap.ofVec ψ.2).onObservables A

/-- Embedding the real vector-state observable expectation back into `ℂ` recovers the canonical
complex expectation exactly. -/
@[simp]
theorem coe_observableExpValue :
    (observableExpValue A ψ : ℂ) = expValue A ψ := by
  simpa [observableExpValue, expValue] using
    (UnitalPositiveLinearMap.coe_onObservables_apply
      (ω := UnitalPositiveLinearMap.ofVec ψ.2) (a := A))

/-- For a self-adjoint observable, the canonical `⟨ψ|A|ψ⟩` orientation also equals
`⟨Aψ|ψ⟩`. -/
theorem expValue_eq_inner_apply_left :
    expValue A ψ = inner ℂ (A.1 ψ.1) ψ.1 := by
  simpa [expValue] using (A.2.isSymmetric ψ.1 ψ.1).symm

/-- Expectation values of observables are real, as required for them to represent
measurable physical quantities. -/
theorem expValue_im_eq_zero : (expValue A ψ).im = 0 := by
  rw [← coe_observableExpValue A ψ]
  simp

/-- The complex vector-state expectation bundled with the proof that it is self-adjoint. -/
noncomputable def expValueSelfAdjoint : selfAdjoint ℂ :=
  ⟨expValue A ψ,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (expValue_im_eq_zero A ψ)⟩

/-- **Phase indeterminacy.** Multiplying a representative by a unit-modulus complex number (a global
phase) does not change the expectation value of any observable. -/
theorem expValue_smul_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) (hψ' : ‖c • ψ.1‖ = 1) :
    expValue A ⟨c • ψ.1, hψ'⟩ = expValue A ψ := by
  simp only [expValue, UnitalPositiveLinearMap.ofVec_apply]
  have h1 : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  simp only [map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, h1, one_mul]

/-- The lossless real vector-state observable expectation is also invariant under global phase. -/
theorem observableExpValue_smul_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1)
    (hψ' : ‖c • ψ.1‖ = 1) :
    observableExpValue A ⟨c • ψ.1, hψ'⟩ = observableExpValue A ψ := by
  apply Complex.ofReal_injective
  calc
    (observableExpValue A ⟨c • ψ.1, hψ'⟩ : ℂ) =
        expValue A ⟨c • ψ.1, hψ'⟩ := coe_observableExpValue A ⟨c • ψ.1, hψ'⟩
    _ = expValue A ψ := expValue_smul_of_norm_eq_one A ψ hc hψ'
    _ = (observableExpValue A ψ : ℂ) := (coe_observableExpValue A ψ).symm

end QuantumTheory