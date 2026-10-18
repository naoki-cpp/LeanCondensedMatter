module

public import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Tactic

public section

set_option linter.style.header false

/-!
# One-dimensional Schwartz Schrödinger dynamics

The one-particle Hamiltonian `H = -κ D² + M_V`, velocity `v = -2iκD/ℏ`, and
Heisenberg localization/current identities specialize the generic Schwartz multiplication
and differential algebra. These are linear endomorphism identities on Schwartz space,
not claims about unbounded operators on `L²`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum
namespace SchwartzSchrodinger1D

open SchwartzKinetic1D
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

/-- Kinetic Schrödinger operator `-κ D²` on Schwartz space. -/
@[expose] noncomputable def kineticOperator (κ : ℝ) : Space →ₗ[ℂ] Space :=
  (-(κ : ℂ)) • derivative.comp derivative

/-- Multiplication-potential Schrödinger operator `-κ D² + M_V` on Schwartz space. -/
@[expose] noncomputable def schrodingerOperator (κ : ℝ) (potential : Space) : Space →ₗ[ℂ] Space :=
  kineticOperator κ + multiplicationOperator potential

/-- Velocity associated with `H = -κ D² + V`, namely `v = -2 i κ D / ℏ`. -/
@[expose] noncomputable def velocityOperator (ℏ κ : ℝ) : Space →ₗ[ℂ] Space :=
  ((2 : ℂ) * (Complex.I / (ℏ : ℂ)) * (-(κ : ℂ))) • derivative


/-- The local multiplication potential contributes no localization commutator. -/
theorem lie_schrodinger_localization_eq_kinetic
    (κ : ℝ) (potential f : Space) :
    ⁅schrodingerOperator κ potential, multiplicationOperator f⁆ =
      ⁅kineticOperator κ, multiplicationOperator f⁆ := by
  simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp]
  rw [schrodingerOperator]
  ext ψ
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  have hcomm' :
      multiplicationOperator potential (multiplicationOperator f ψ) =
        multiplicationOperator f (multiplicationOperator potential ψ) := by
    ext x
    change potential x * (f x * ψ x) = f x * (potential x * ψ x)
    ring
  rw [hcomm']
  abel

/-- Schrödinger localization has the standard first-order Heisenberg current form
`(i/ℏ)[H,M_f] = 1/2 {M_(D f),v}` on complex Schwartz space. -/
theorem heisenberg_localization_eq_symmetrized_velocity
    (ℏ κ : ℝ) (potential f : Space) :
    (Complex.I / (ℏ : ℂ)) •
        ⁅schrodingerOperator κ potential, multiplicationOperator f⁆ =
      (1 / 2 : ℂ) •
        ((multiplicationOperator (derivative f)).comp (velocityOperator ℏ κ) +
          (velocityOperator ℏ κ).comp (multiplicationOperator (derivative f))) := by
  rw [lie_schrodinger_localization_eq_kinetic]
  apply LinearMap.ext
  intro ψ
  simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.add_apply, kineticOperator, velocityOperator]
  rw [secondDerivative_multiplication_apply]
  rw [derivative_multiplication_apply]
  simp only [map_smul]
  module
end
end SchwartzSchrodinger1D
end Continuum
end SingleParticle
end QuantumMechanics
