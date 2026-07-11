import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Axiomatic quantum theory: minimal postulates

Minimal formalization of the standard (Dirac–von Neumann) axiomatic quantum theory:
the state space postulate, the definition of an observable, and the expectation
value they jointly define.

See `notes/model-and-assumptions.md` for the physics-to-Lean correspondence and
scope notes.
-/

namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **State space postulate.** A pure state of a quantum system is a unit vector in a
complex Hilbert space `H`. (Global-phase equivalence of states is not yet formalized;
`State H` is the space of representatives, not of physical states.) -/
def State (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  { ψ : H // ‖ψ‖ = 1 }

/-- **Observable (definition).** An observable is a self-adjoint bounded linear operator
on the state space. Self-adjointness is what makes `expValue_im_eq_zero` below hold; it is
not an independent postulate but the defining property that makes an operator eligible to
represent a measurable physical quantity. -/
def Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  { A : H →L[ℂ] H // IsSelfAdjoint A }

variable (A : Observable H) (ψ : State H)

/-- The expectation value of an observable `A` in a state `ψ`, `⟨ψ|A|ψ⟩`. -/
noncomputable def expValue : ℂ := inner ℂ (A.1 ψ.1) ψ.1

/-- Expectation values of observables are real, as required for them to represent
measurable physical quantities. -/
theorem expValue_im_eq_zero : (expValue A ψ).im = 0 :=
  A.2.isSymmetric.im_inner_apply_self ψ.1

/-- **Phase indeterminacy.** Multiplying a state by a unit-modulus complex number (a global
phase) does not change the expectation value of any observable — quantum states are physically
determined only up to a global phase. -/
theorem expValue_smul_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) (hψ' : ‖c • ψ.1‖ = 1) :
    expValue A ⟨c • ψ.1, hψ'⟩ = expValue A ψ := by
  have h1 : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; norm_num
  simp only [expValue, map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, h1, one_mul]

end QuantumTheory
