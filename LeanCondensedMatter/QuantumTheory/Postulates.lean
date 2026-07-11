import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Axiomatic quantum theory: minimal postulates

Minimal formalization of the standard (Dirac–von Neumann) axiomatic postulates of
quantum theory: the state space postulate and the observable postulate, together
with the expectation value they define.

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

/-- **Observable postulate.** An observable is a self-adjoint bounded linear operator
on the state space. -/
def Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  { A : H →L[ℂ] H // IsSelfAdjoint A }

variable (A : Observable H) (ψ : State H)

/-- The expectation value of an observable `A` in a state `ψ`, `⟨ψ|A|ψ⟩`. -/
noncomputable def expValue : ℂ := inner ℂ (A.1 ψ.1) ψ.1

/-- Expectation values of observables are real, as required for them to represent
measurable physical quantities. -/
theorem expValue_im_eq_zero : (expValue A ψ).im = 0 :=
  A.2.isSymmetric.im_inner_apply_self ψ.1

end QuantumTheory
