import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Complex.Module

set_option linter.style.header false

/-!
# Axiomatic quantum theory: minimal postulates

Minimal formalization of the standard (Dirac–von Neumann) axiomatic quantum theory:
the state space postulate, the definition of an observable, and the expectation
value they jointly define.

See `notes/model-and-assumptions.md` for the physics-to-Lean correspondence and
scope notes.
-/

namespace QuantumTheory

/-- **State space postulate.** A pure state of a quantum system is represented by a unit vector in
a complex Hilbert space `H`. `State H` is the space of unit-vector representatives rather than a
quotient by global phase; phase invariance is expressed by the theorems below. -/
def State (H : Type*) [NormedAddCommGroup H] :=
  { ψ : H // ‖ψ‖ = 1 }

/-- **Observable (definition).** An observable is a self-adjoint bounded linear operator
on the state space. Self-adjointness is what makes `expValue_im_eq_zero` below hold; it is
not an independent postulate but the defining property that makes an operator eligible to
represent a measurable physical quantity. -/
def Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  { A : H →L[ℂ] H // IsSelfAdjoint A }

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : Observable H) (ψ : State H)

/-- The canonical complex expectation of an observable `A` in a state `ψ`, `⟨ψ|A|ψ⟩`. -/
noncomputable def expValue : ℂ := inner ℂ ψ.1 (A.1 ψ.1)

/-- For a self-adjoint observable, the canonical `⟨ψ|A|ψ⟩` orientation also equals
`⟨Aψ|ψ⟩`. -/
theorem expValue_eq_inner_apply_left :
    expValue A ψ = inner ℂ (A.1 ψ.1) ψ.1 :=
  (A.2.isSymmetric ψ.1 ψ.1).symm

/-- Expectation values of observables are real, as required for them to represent
measurable physical quantities. -/
theorem expValue_im_eq_zero : (expValue A ψ).im = 0 := by
  simpa [expValue] using A.2.isSymmetric.im_inner_self_apply ψ.1

/-- The complex pure-state expectation bundled with the proof that it is self-adjoint. -/
noncomputable def expValueSelfAdjoint : selfAdjoint ℂ :=
  ⟨expValue A ψ,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (expValue_im_eq_zero A ψ)⟩

/-- The real expectation value of an observable in a pure state, obtained losslessly from the
proved-self-adjoint complex expectation rather than by projecting an arbitrary scalar with `.re`. -/
noncomputable def observableExpValue : ℝ :=
  Complex.selfAdjointEquiv (expValueSelfAdjoint A ψ)

/-- Embedding the real pure-state observable expectation back into `ℂ` recovers the canonical
complex expectation exactly. -/
@[simp]
theorem coe_observableExpValue :
    (observableExpValue A ψ : ℂ) = expValue A ψ := by
  apply Complex.ext
  · rfl
  · simpa [observableExpValue, expValueSelfAdjoint, Complex.selfAdjointEquiv] using
      (expValue_im_eq_zero A ψ).symm

/-- **Phase indeterminacy.** Multiplying a state by a unit-modulus complex number (a global
phase) does not change the expectation value of any observable — quantum states are physically
determined only up to a global phase. -/
theorem expValue_smul_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) (hψ' : ‖c • ψ.1‖ = 1) :
    expValue A ⟨c • ψ.1, hψ'⟩ = expValue A ψ := by
  change inner ℂ (c • ψ.1) (A.1 (c • ψ.1)) = inner ℂ ψ.1 (A.1 ψ.1)
  have h1 : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; norm_num
  simp only [map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, h1, one_mul]

/-- The lossless real pure-state observable expectation is also invariant under global phase. -/
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
