import LeanCondensedMatter.QuantumTheory.LinearResponse.FreeDynamics

set_option linter.style.header false

/-!
# Bounded pure-state dynamics

This module uses norm preservation of the bounded free propagator to define the canonical
Schrödinger-picture evolution of normalized pure states. The API keeps vector representatives
rather than quotienting by global phase; phase compatibility is expressed by an exact theorem.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- A bounded free propagator preserves vector norms. -/
@[simp]
theorem norm_freePropagator_apply (t : ℝ) (x : H) :
    ‖freePropagator system t x‖ = ‖x‖ := by
  have hcomp :
      ContinuousLinearMap.adjoint (freePropagator system t) ∘SL
          freePropagator system t = 1 := by
    ext y
    have h := congrArg (fun U : H →L[ℂ] H => U y)
      (star_mul_freePropagator system t)
    change ContinuousLinearMap.adjoint (freePropagator system t)
        (freePropagator system t y) = y at h
    exact h
  exact
    ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (freePropagator system t)).2 hcomp) x

/-- Multiplication of a normalized state representative by a unit complex phase. -/
def phaseState (c : ℂ) (hc : ‖c‖ = 1) (ψ : State H) : State H :=
  ⟨c • ψ.1, by rw [norm_smul, hc, ψ.2, one_mul]⟩

omit [CompleteSpace H] in
@[simp]
theorem phaseState_val (c : ℂ) (hc : ‖c‖ = 1) (ψ : State H) :
    (phaseState c hc ψ).1 = c • ψ.1 :=
  rfl

/-- Schrödinger-picture evolution of a normalized pure state. -/
noncomputable def evolveState (ψ : State H) (t : ℝ) : State H :=
  ⟨freePropagator system t ψ.1, by simp [ψ.2]⟩

@[simp]
theorem evolveState_val (ψ : State H) (t : ℝ) :
    (evolveState system ψ t).1 = freePropagator system t ψ.1 :=
  rfl

/-- Pure-state evolution is the identity at time zero. -/
@[simp]
theorem evolveState_zero (ψ : State H) :
    evolveState system ψ 0 = ψ := by
  ext
  simp [evolveState]

/-- Pure-state evolution is an action of additive time. -/
theorem evolveState_add (ψ : State H) (t s : ℝ) :
    evolveState system (evolveState system ψ s) t =
      evolveState system ψ (t + s) := by
  ext
  change freePropagator system t (freePropagator system s ψ.1) =
    freePropagator system (t + s) ψ.1
  simpa [mul_apply_eq_comp] using
    congrArg (fun U : H →L[ℂ] H => U ψ.1) (freePropagator_add system t s).symm

/-- Negative-time evolution undoes positive-time evolution. -/
@[simp]
theorem evolveState_neg_after (ψ : State H) (t : ℝ) :
    evolveState system (evolveState system ψ t) (-t) = ψ := by
  ext
  change freePropagator system (-t) (freePropagator system t ψ.1) = ψ.1
  simpa [mul_apply_eq_comp] using
    congrArg (fun U : H →L[ℂ] H => U ψ.1) (freePropagator_neg_mul system t)

/-- Positive-time evolution undoes negative-time evolution. -/
@[simp]
theorem evolveState_after_neg (ψ : State H) (t : ℝ) :
    evolveState system (evolveState system ψ (-t)) t = ψ := by
  ext
  change freePropagator system t (freePropagator system (-t) ψ.1) = ψ.1
  simpa [mul_apply_eq_comp] using
    congrArg (fun U : H →L[ℂ] H => U ψ.1) (freePropagator_mul_neg system t)

/-- Schrödinger evolution commutes exactly with a change of global-phase representative. -/
@[simp]
theorem evolveState_phaseState (ψ : State H) (c : ℂ) (hc : ‖c‖ = 1) (t : ℝ) :
    evolveState system (phaseState c hc ψ) t =
      phaseState c hc (evolveState system ψ t) := by
  ext
  simp [evolveState, phaseState]

end
end LinearResponse
end QuantumTheory
