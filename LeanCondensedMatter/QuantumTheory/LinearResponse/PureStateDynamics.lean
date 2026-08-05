import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics
import Mathlib.Algebra.Star.Unitary

set_option linter.style.header false

/-!
# Bounded pure-state dynamics

This module exposes the unitary content of the bounded free propagator and uses it to define the
canonical Schrödinger-picture evolution of normalized pure states. The API keeps vector
representatives rather than quotienting by global phase; phase compatibility is expressed by an
exact theorem.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- The adjoint of the free propagator is its left inverse. -/
@[simp]
theorem star_mul_freePropagator (t : ℝ) :
    star (freePropagator system t) * freePropagator system t = 1 := by
  rw [star_freePropagator]
  exact freePropagator_neg_mul system t

/-- The adjoint of the free propagator is its right inverse. -/
@[simp]
theorem freePropagator_mul_star (t : ℝ) :
    freePropagator system t * star (freePropagator system t) = 1 := by
  rw [star_freePropagator]
  exact freePropagator_mul_neg system t

/-- Every bounded free propagator is a unitary element of the endomorphism algebra. -/
theorem freePropagator_mem_unitary (t : ℝ) :
    freePropagator system t ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  exact ⟨star_mul_freePropagator system t, freePropagator_mul_star system t⟩

/-- The bounded free propagator bundled as a unitary operator. -/
noncomputable def freePropagatorUnitary (t : ℝ) : unitary (H →L[ℂ] H) :=
  ⟨freePropagator system t, freePropagator_mem_unitary system t⟩

@[simp]
theorem coe_freePropagatorUnitary (t : ℝ) :
    (freePropagatorUnitary system t : H →L[ℂ] H) = freePropagator system t :=
  rfl

/-- A bounded free propagator preserves vector norms. -/
@[simp]
theorem norm_freePropagator_apply (t : ℝ) (x : H) :
    ‖freePropagator system t x‖ = ‖x‖ := by
  have hcomp :
      ContinuousLinearMap.adjoint (freePropagator system t) ∘SL
          freePropagator system t = 1 := by
    simpa using star_mul_freePropagator system t
  exact
    ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (freePropagator system t)).2 hcomp) x

/-- Multiplication of a normalized state representative by a unit complex phase. -/
def State.phaseSmul (c : ℂ) (hc : ‖c‖ = 1) (ψ : State H) : State H :=
  ⟨c • ψ.1, by rw [norm_smul, hc, ψ.2, one_mul]⟩

@[simp]
theorem State.coe_phaseSmul (c : ℂ) (hc : ‖c‖ = 1) (ψ : State H) :
    (ψ.phaseSmul c hc : H) = c • ψ.1 :=
  rfl

/-- Schrödinger-picture evolution of a normalized pure state. -/
noncomputable def evolveState (ψ : State H) (t : ℝ) : State H :=
  ⟨freePropagator system t ψ.1, by simp [ψ.2]⟩

@[simp]
theorem coe_evolveState (ψ : State H) (t : ℝ) :
    (evolveState system ψ t : H) = freePropagator system t ψ.1 :=
  rfl

/-- Pure-state evolution is the identity at time zero. -/
@[simp]
theorem evolveState_zero (ψ : State H) :
    evolveState system ψ 0 = ψ := by
  apply Subtype.ext
  simp [evolveState]

/-- Pure-state evolution is an action of additive time. -/
theorem evolveState_add (ψ : State H) (t s : ℝ) :
    evolveState system (evolveState system ψ s) t =
      evolveState system ψ (t + s) := by
  apply Subtype.ext
  change freePropagator system t (freePropagator system s ψ.1) =
    freePropagator system (t + s) ψ.1
  simpa [mul_apply_eq_comp] using
    congrArg (fun U : H →L[ℂ] H => U ψ.1) (freePropagator_add system t s).symm

/-- Negative-time evolution undoes positive-time evolution. -/
@[simp]
theorem evolveState_neg_after (ψ : State H) (t : ℝ) :
    evolveState system (evolveState system ψ t) (-t) = ψ := by
  apply Subtype.ext
  change freePropagator system (-t) (freePropagator system t ψ.1) = ψ.1
  simpa [mul_apply_eq_comp] using
    congrArg (fun U : H →L[ℂ] H => U ψ.1) (freePropagator_neg_mul system t)

/-- Positive-time evolution undoes negative-time evolution. -/
@[simp]
theorem evolveState_after_neg (ψ : State H) (t : ℝ) :
    evolveState system (evolveState system ψ (-t)) t = ψ := by
  apply Subtype.ext
  change freePropagator system t (freePropagator system (-t) ψ.1) = ψ.1
  simpa [mul_apply_eq_comp] using
    congrArg (fun U : H →L[ℂ] H => U ψ.1) (freePropagator_mul_neg system t)

/-- Schrödinger evolution commutes exactly with a change of global-phase representative. -/
@[simp]
theorem evolveState_phaseSmul (ψ : State H) (c : ℂ) (hc : ‖c‖ = 1) (t : ℝ) :
    evolveState system (ψ.phaseSmul c hc) t =
      (evolveState system ψ t).phaseSmul c hc := by
  apply Subtype.ext
  simp [evolveState, State.phaseSmul]

end
end LinearResponse
end QuantumTheory
