import LeanCondensedMatter.Analysis.ODE
import LeanCondensedMatter.Models.OrbitalRelaxation.Finite
import LeanCondensedMatter.Analysis.Geometry.FiniteAngularKernel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

set_option linter.style.header false

/-!
# Conditional orbital relaxation from a stationary quadrupole mode

This finite-mode kinetic benchmark combines the exact orbital double-commutator
coefficient with the degree-two eigenmode of a supplied angular collision
kernel. It explicitly assumes a quasistationary quadrupole balance and a
polarization-to-quadrupole dynamical coupling; these assumptions constitute a
second-order kinetic closure, not consequences of the matrix Hamiltonian.

The resulting exponential law follows from the scalar decay equation in
`Analysis.ODE` and applies to the specified finite-mode closure.
It does not derive the collision moments from a continuous kernel or establish
a controlled microscopic approximation. The continuous spherical average of the
quartic double commutator is a separate result in `OrbitalRelaxation.SphereMoments`.

Physical motivation: Sohn, Lee, and Lee, Phys. Rev. Lett. 132, 246301 (2024),
supplemental Sec. I.A.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

open FiniteAngularKernel

variable {Ω : Type*} [Fintype Ω]

/-- A finite, quasistationary degree-two kinetic closure for one orbital
polarization component. The quadrupole is assumed to occupy the specified
traceless mode, whose collision eigenvalue is supplied by `AngularKernelMoments`.

The stationary balance and polarization equation are physical closure
assumptions. The collision eigenmode identity and quartic matrix coefficient
are independently verified, but their microscopic coupling is not derived. -/
structure QuasistationaryOrbitalKineticClosure
    (data : AngularKernelMoments Ω) (axis i j : Fin 3)
    (ℏ c₁ c₂ r : ℝ) where
  /-- Observable orbital polarization of the selected Cartesian component. -/
  polarization : ℝ → ℝ
  /-- Amplitude of the selected traceless degree-two angular mode. -/
  quadrupoleAmplitude : ℝ → ℝ
  /-- Strictly positive second-harmonic collision rate. -/
  degreeTwoRate_pos : 0 < data.degreeTwoRate
  /-- Positive Planck constant for the physical interpretation. -/
  hbar_pos : 0 < ℏ
  /-- The selected angular quadrupole is observable on the finite grid. -/
  mode_nonzero : ∃ p, quadrupoleMode data.direction i j p ≠ 0
  /-- Quasistationary balance between collision loss and polarization source. -/
  stationary_quadrupole : ∀ t p,
    angularCollision data.kernel
        (fun q => quadrupoleAmplitude t * quadrupoleMode data.direction i j q) p =
      -(polarization t) * quadrupoleMode data.direction i j p
  /-- Phenomenological orbital-to-quadrupole coupling, with the *proved*
  matrix coefficient and finite quartic cubature. This is not a microscopic
  kinetic equation derived from the Hamiltonian. -/
  polarization_dynamics : ∀ t,
    HasDerivAt polarization
      (-(evenQuarticCubature r (orbitalDoubleCommutator axis c₁ c₂) / ℏ ^ 2 *
          quadrupoleAmplitude t)) t

namespace QuasistationaryOrbitalKineticClosure

variable {data : AngularKernelMoments Ω} {axis i j : Fin 3}
variable {ℏ c₁ c₂ r : ℝ}
variable (closure : QuasistationaryOrbitalKineticClosure data axis i j ℏ c₁ c₂ r)

/-- The collision eigenvalue determines the stationary quadrupole response.
This step requires a nonzero mode on the finite angular grid. -/
theorem quadrupoleAmplitude_eq (t : ℝ) :
    closure.quadrupoleAmplitude t =
      degreeTwoTime data.degreeTwoRate * closure.polarization t := by
  obtain ⟨p, hp⟩ := closure.mode_nonzero
  have hs := closure.stationary_quadrupole t p
  rw [angularCollision_const_mul, data.collision_quadrupole] at hs
  have heq : closure.quadrupoleAmplitude t * data.degreeTwoRate =
      closure.polarization t := by
    apply mul_right_cancel₀ hp
    nlinarith [hs]
  simpa only [degreeTwoTime, momentumTime, div_eq_mul_inv, mul_comm] using
    ((eq_div_iff (ne_of_gt closure.degreeTwoRate_pos)).mpr heq)

/-- The orbital polarization obeys a decay equation with a coefficient
identified from the finite double commutator and the degree-two collision
eigenvalue. The dynamical coupling is supplied by the named closure. -/
theorem hasDerivAt_polarization (t : ℝ) :
    HasDerivAt closure.polarization
      (-(orbitalRate axis ℏ (degreeTwoTime data.degreeTwoRate) c₁ c₂ r *
          closure.polarization t)) t := by
  convert closure.polarization_dynamics t using 1
  rw [closure.quadrupoleAmplitude_eq t]
  simp only [orbitalRate, degreeTwoTime, momentumTime]
  ring

/-- The finite quasistationary closure has a unique global polarization
trajectory determined by its value at time zero. This statement is conditional
on the closure holding at every real time, not an unconditional material law. -/
theorem polarization_eq_exp (t : ℝ) :
    closure.polarization t =
      closure.polarization 0 *
        Real.exp (-(orbitalRate axis ℏ (degreeTwoTime data.degreeTwoRate) c₁ c₂ r * t)) :=
  Real.eq_initial_mul_exp_neg_of_hasDerivAt
    (orbitalRate axis ℏ (degreeTwoTime data.degreeTwoRate) c₁ c₂ r)
    closure.polarization closure.hasDerivAt_polarization t

end QuasistationaryOrbitalKineticClosure

end QuantumTheory.Models.OrbitalRelaxation
