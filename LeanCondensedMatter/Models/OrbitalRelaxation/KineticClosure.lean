import LeanCondensedMatter.Models.OrbitalRelaxation.AngularCollision
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

The resulting exponential law is for this specified finite-mode closure.
No assertion is made that the finite cubature equals the full spherical integral,
that the collision moments follow from an isotropic continuous kernel, or that
the closure is a controlled microscopic approximation.

Physical motivation: Sohn, Lee, and Lee, Phys. Rev. Lett. 132, 246301 (2024),
supplemental Sec. I.A.
-/

namespace QuantumTheory.Models.OrbitalRelaxation

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
  have hmult :
      (closure.quadrupoleAmplitude t * data.degreeTwoRate -
          closure.polarization t) * quadrupoleMode data.direction i j p = 0 := by
    nlinarith [hs]
  have heq : closure.quadrupoleAmplitude t * data.degreeTwoRate =
      closure.polarization t :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmult).resolve_right hp)
  have hrate : data.degreeTwoRate ≠ 0 := ne_of_gt closure.degreeTwoRate_pos
  calc
    closure.quadrupoleAmplitude t =
        closure.polarization t / data.degreeTwoRate :=
          (eq_div_iff hrate).mpr heq
    _ = degreeTwoTime data.degreeTwoRate * closure.polarization t := by
          simp only [degreeTwoTime, momentumTime, div_eq_mul_inv]
          ring

/-- The orbital polarization obeys a decay equation with a coefficient
identified from the finite double commutator and the degree-two collision
eigenvalue. The dynamical coupling is supplied by the named closure. -/
theorem hasDerivAt_polarization (t : ℝ) :
    HasDerivAt closure.polarization
      (-(orbitalRate axis ℏ (degreeTwoTime data.degreeTwoRate) c₁ c₂ r *
          closure.polarization t)) t := by
  have hcoefficient :
      -(evenQuarticCubature r (orbitalDoubleCommutator axis c₁ c₂) / ℏ ^ 2 *
          closure.quadrupoleAmplitude t) =
        -(orbitalRate axis ℏ (degreeTwoTime data.degreeTwoRate) c₁ c₂ r *
          closure.polarization t) := by
    rw [closure.quadrupoleAmplitude_eq t]
    simp only [orbitalRate, degreeTwoTime, momentumTime]
    ring
  rw [← hcoefficient]
  exact closure.polarization_dynamics t

private theorem scalar_decay_solution (rate : ℝ) (f : ℝ → ℝ)
    (hderiv : ∀ t, HasDerivAt f (-(rate * f t)) t) (t : ℝ) :
    f t = f 0 * Real.exp (-(rate * t)) := by
  let g : ℝ → ℝ := fun s => f s * Real.exp (rate * s)
  have hgzero (s : ℝ) : HasDerivAt g 0 s := by
    have he : HasDerivAt (fun u : ℝ => Real.exp (rate * u))
        (Real.exp (rate * s) * rate) s := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id s).const_mul rate).exp)
    change HasDerivAt (fun u : ℝ => f u * Real.exp (rate * u)) 0 s
    convert (hderiv s).mul he using 1
    ring
  have hdiff : Differentiable ℝ g := fun s => (hgzero s).differentiableAt
  have hzero : ∀ s, deriv g s = 0 := fun s => (hgzero s).deriv
  have hconst : g t = g 0 := is_const_of_deriv_eq_zero hdiff hzero t 0
  have hproduct : f t * Real.exp (rate * t) = f 0 := by
    simpa [g] using hconst
  calc
    f t = (f t * Real.exp (rate * t)) * Real.exp (-(rate * t)) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ = f 0 * Real.exp (-(rate * t)) := by rw [hproduct]

/-- The finite quasistationary closure has a unique global polarization
trajectory determined by its value at time zero. This statement is conditional
on the closure holding at every real time, not an unconditional material law. -/
theorem polarization_eq_exp (t : ℝ) :
    closure.polarization t =
      closure.polarization 0 *
        Real.exp (-(orbitalRate axis ℏ (degreeTwoTime data.degreeTwoRate) c₁ c₂ r * t)) :=
  scalar_decay_solution
    (orbitalRate axis ℏ (degreeTwoTime data.degreeTwoRate) c₁ c₂ r)
    closure.polarization closure.hasDerivAt_polarization t

end QuasistationaryOrbitalKineticClosure

end QuantumTheory.Models.OrbitalRelaxation
