import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerEvolutionProbability1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuitySchwartzTotal1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Schwartz representatives of continuum Schrödinger evolution

Strong differentiability of an `L²` trajectory does not by itself provide pointwise time
differentiability of a chosen representative. This module keeps that distinction explicit.

A `ContinuumSchwartzEvolutionRepresentative1D` consists of a Schwartz-valued representative family
whose `L²` image is the abstract unitary trajectory, together with the additional pointwise time
derivative and Schrödinger-equation data needed by the local continuity API from #705.

This lets the operator-theoretic and pointwise developments meet without deriving unjustified
representative regularity from Hilbert-space differentiability.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace SchwartzMap

variable {κ : ℝ} {potential : ℝ → ℝ}
variable {hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)}

/-- A Schwartz representative of an abstract continuum Schrödinger evolution, with the additional
pointwise regularity required to invoke the local and weak continuity equations.

The `represents_propagator` field is the operator-theoretic connection. The derivative and
pointwise Schrödinger fields are deliberately separate assumptions: they are not consequences of
strong `L²` differentiability alone. -/
structure ContinuumSchwartzEvolutionRepresentative1D
    (evolution : ContinuumSchrodingerEvolution1D κ potential hpotential) where
  /-- Schwartz representative at each time. -/
  wavefunction : ℝ → SchwartzMap ℝ ℂ
  /-- Chosen pointwise time derivative of the representative. -/
  timeDerivative : ℝ → ℝ → ℂ
  /-- The representative family agrees with the abstract propagator trajectory in `L²`. -/
  represents_propagator : ∀ t,
    (wavefunction t).toLp 2 (volume : Measure ℝ) =
      evolution.propagator t ((wavefunction 0).toLp 2 (volume : Measure ℝ))
  /-- Pointwise real-part time differentiability. -/
  hasDerivAt_re : ∀ t x,
    HasDerivAt (fun τ : ℝ => (wavefunction τ x).re) (timeDerivative t x).re t
  /-- Pointwise imaginary-part time differentiability. -/
  hasDerivAt_im : ∀ t x,
    HasDerivAt (fun τ : ℝ => (wavefunction τ x).im) (timeDerivative t x).im t
  /-- The chosen representative and time derivative satisfy the pointwise Schrödinger equation. -/
  schrodinger : ∀ t x,
    Complex.I * (evolution.hbar : ℂ) * timeDerivative t x =
      -(κ : ℂ) * schwartzSpatialSecondDerivative1D (wavefunction t) x +
        (potential x : ℂ) * wavefunction t x

variable {evolution : ContinuumSchrodingerEvolution1D κ potential hpotential}
variable (representative : ContinuumSchwartzEvolutionRepresentative1D evolution)

/-- The representative probability density has the expected pointwise time derivative. -/
theorem ContinuumSchwartzEvolutionRepresentative1D.hasDerivAt_probabilityDensity
    (t x : ℝ) :
    HasDerivAt
      (fun τ : ℝ => probabilityDensityValue (representative.wavefunction τ x))
      (probabilityDensityTimeDerivativeValue
        (representative.wavefunction t x) (representative.timeDerivative t x)) t :=
  hasDerivAt_probabilityDensityValue
    (representative.hasDerivAt_re t x) (representative.hasDerivAt_im t x)

/-- The operator-generated Schwartz representative satisfies the pointwise continuity equation. -/
theorem ContinuumSchwartzEvolutionRepresentative1D.pointwise_continuity
    (t x : ℝ) :
    deriv (fun τ : ℝ => probabilityDensityValue (representative.wavefunction τ x)) t +
      deriv (fun y : ℝ => probabilityCurrentValue1D evolution.hbar κ
        (representative.wavefunction t y)
        (schwartzSpatialDerivative1D (representative.wavefunction t) y)) x = 0 := by
  apply oneDimensional_schrodinger_continuity_of_schwartz
    evolution.hbar κ (potential x) evolution.hbar_ne_zero
    (ψTime := fun τ : ℝ => representative.wavefunction τ x)
    (ψSpace := representative.wavefunction t)
    (ψt := representative.timeDerivative t x)
    (t := t) (x := x)
  · rfl
  · exact representative.hasDerivAt_re t x
  · exact representative.hasDerivAt_im t x
  · exact representative.schrodinger t x

/-- Interval-weak continuity for an operator-generated Schwartz representative. The test-function
and current-divergence integrability hypotheses are exactly those of the existing #705 theorem. -/
theorem ContinuumSchwartzEvolutionRepresentative1D.weak_continuity_interval
    (t a b : ℝ)
    {test testDerivative : ℝ → ℝ}
    (htest : ∀ x ∈ Set.uIcc a b, HasDerivAt test (testDerivative x) x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D evolution.hbar κ
        (representative.wavefunction t x)
        (schwartzSpatialSecondDerivative1D (representative.wavefunction t) x)) volume a b) :
    intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue
          (representative.wavefunction t x) (representative.timeDerivative t x)) =
      intervalSmearedCurrentPairing1D a b testDerivative
          (fun x => probabilityCurrentValue1D evolution.hbar κ
            (representative.wavefunction t x)
            (schwartzSpatialDerivative1D (representative.wavefunction t) x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => probabilityCurrentValue1D evolution.hbar κ
            (representative.wavefunction t x)
            (schwartzSpatialDerivative1D (representative.wavefunction t) x)) := by
  exact schrodinger_weak_continuity_interval_of_schwartz
    a b evolution.hbar κ evolution.hbar_ne_zero
    (representative.wavefunction t)
    htest (representative.schrodinger t) htestIntegrable hcurrentIntegrable

/-- The whole-space integral of the local probability-density rate vanishes for the representative.
This is the local-continuity side of total probability conservation. -/
theorem ContinuumSchwartzEvolutionRepresentative1D.integral_density_rate_eq_zero
    (t : ℝ) :
    (∫ x, probabilityDensityTimeDerivativeValue
      (representative.wavefunction t x) (representative.timeDerivative t x)) = 0 :=
  integral_probabilityDensityTimeDerivativeValue_of_schrodinger_schwartz_eq_zero
    evolution.hbar κ evolution.hbar_ne_zero
    (representative.wavefunction t) (representative.schrodinger t)

/-- The same Schwartz representative has exactly conserved Born probability by the unitary `L²`
evolution. This is the global operator-theoretic side of the bridge. -/
theorem ContinuumSchwartzEvolutionRepresentative1D.totalProbability_eq_initial
    (t : ℝ) :
    totalProbability1D (fun x => representative.wavefunction t x) =
      totalProbability1D (fun x => representative.wavefunction 0 x) :=
  evolution.totalProbability1D_schwartz_eq_initial
    representative.wavefunction representative.represents_propagator t

end
end Continuum
end SingleParticle
end QuantumMechanics
