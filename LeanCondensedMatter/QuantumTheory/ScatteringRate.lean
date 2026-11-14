import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Single-particle damping convention

A pole with damping half-width Γ uses the single-particle rate 2Γ/ℏ and its reciprocal
lifetime. These scalar conventions are independent of the Hamiltonian, impurity model,
and transport relaxation time. They do not identify an arbitrary self-energy with a
physical exponential decay or establish Fermi's golden rule.

The functions are total: inverse zero is zero in Lean, not an infinite lifetime.
A physical finite lifetime requires positive ℏ and positive damping.
-/

namespace QuantumTheory

noncomputable section

/-- Single-particle probability-decay rate associated with a supplied damping half-width. -/
def scatteringRateOfDamping (hbar damping : ℝ) : ℝ := 2 * damping / hbar

/-- Reciprocal single-particle rate; interpreted as a finite lifetime for positive inputs. -/
def lifetimeOfDamping (hbar damping : ℝ) : ℝ := (scatteringRateOfDamping hbar damping)⁻¹

theorem scatteringRateOfDamping_pos {hbar damping : ℝ}
    (hhbar : 0 < hbar) (hdamping : 0 < damping) :
    0 < scatteringRateOfDamping hbar damping := by
  exact div_pos (mul_pos (by positivity) hdamping) hhbar

theorem lifetimeOfDamping_pos {hbar damping : ℝ}
    (hhbar : 0 < hbar) (hdamping : 0 < damping) :
    0 < lifetimeOfDamping hbar damping := by
  exact inv_pos.mpr (scatteringRateOfDamping_pos hhbar hdamping)

/-- The pole half-width is half of ℏ times the corresponding probability-decay rate. -/
theorem damping_eq_half_hbar_mul_rate (hbar damping : ℝ) (hhbar : hbar ≠ 0) :
    damping = (hbar / 2) * scatteringRateOfDamping hbar damping := by
  unfold scatteringRateOfDamping
  field_simp [hhbar]

/-- Equivalent lifetime convention, stated without model-specific nonvanishing assumptions. -/
theorem damping_eq_hbar_div_two_lifetime (hbar damping : ℝ) (hhbar : hbar ≠ 0) :
    damping = hbar / (2 * lifetimeOfDamping hbar damping) := by
  by_cases hdamping : damping = 0
  · simp [hdamping, lifetimeOfDamping, scatteringRateOfDamping]
  · unfold lifetimeOfDamping scatteringRateOfDamping
    field_simp [hhbar, hdamping]

/-- For the scalar damped-pole ansatz, squaring the amplitude doubles the exponent.
This proves the rate convention for that ansatz, not exponential decay for a general Hamiltonian. -/
theorem norm_exp_dampedPole_sq (hbar energy damping time : ℝ) :
    ‖Complex.exp (-((damping * time / hbar : ℝ) : ℂ) -
        Complex.I * ((energy * time / hbar : ℝ) : ℂ))‖ ^ 2 =
      Real.exp (-scatteringRateOfDamping hbar damping * time) := by
  rw [Complex.norm_exp]
  have hre :
      (-((damping * time / hbar : ℝ) : ℂ) -
        Complex.I * ((energy * time / hbar : ℝ) : ℂ)).re =
        -(damping * time / hbar) := by simp
  rw [hre, pow_two, ← Real.exp_add]
  congr 1
  unfold scatteringRateOfDamping
  ring

end
end QuantumTheory
