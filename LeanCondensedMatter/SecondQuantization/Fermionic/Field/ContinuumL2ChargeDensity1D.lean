import LeanCondensedMatter.Analysis.Operator.L2MultiplicationRealLine.Linear
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `L²` continuum charge density on the one-particle sector

This module connects the algebraic smeared fermionic charge-density interface to the canonical
bounded multiplication operators on `L²(ℝ, ℂ)` supplied by the analysis layer.

The smearing space is `L∞(ℝ, ℂ)`. Its canonical multiplication family is complex-linear and may
therefore be fed directly into `chargeDensity`, giving

```text
ρ_q(f) = q dΓ(M_f).
```

On the one-particle sector this acts exactly as the bounded analytic operator `q M_f`. In
particular, for a bounded real test function this is the same operator whose `L²` expectation is
identified with `∫ f(x) q |ψ(x)|² dx` in the one-particle continuum layer, without introducing a
direct dependency between `SecondQuantization` and `QuantumMechanics.SingleParticle`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- The canonical one-dimensional continuum `L²` one-particle space used by the analytic
multiplication-operator layer. -/
abbrev ContinuumL2Wavefunction1D := L2MultiplicationRealLine.ComplexL2

/-- The canonical `L∞(ℝ, ℂ)` smearing space for bounded continuum density observables. -/
abbrev ContinuumLInfMultiplier1D := L2MultiplicationRealLine.ComplexLInf

/-- The canonical `L²` multiplication family, viewed as algebraic linear endomorphisms so it can be
second-quantized. -/
noncomputable def continuumL2Multiplication1D :
    ContinuumLInfMultiplier1D →ₗ[ℂ]
      (ContinuumL2Wavefunction1D →ₗ[ℂ] ContinuumL2Wavefunction1D) :=
  L2MultiplicationRealLine.multiplicationLinear

@[simp]
theorem continuumL2Multiplication1D_apply
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    continuumL2Multiplication1D f ψ =
      L2MultiplicationRealLine.multiplicationOperator f ψ :=
  rfl

/-- The abstract fermionic charge density specialized to canonical bounded multiplication on
`L²(ℝ, ℂ)`. -/
noncomputable def continuumL2ChargeDensity1D (q : ℂ) :
    ContinuumLInfMultiplier1D →ₗ[ℂ]
      (AlgebraicFock ContinuumL2Wavefunction1D →ₗ[ℂ]
        AlgebraicFock ContinuumL2Wavefunction1D) :=
  chargeDensity ContinuumL2Wavefunction1D q continuumL2Multiplication1D

@[simp]
theorem continuumL2ChargeDensity1D_apply
    (q : ℂ) (f : ContinuumLInfMultiplier1D) :
    continuumL2ChargeDensity1D q f =
      q • AlgebraicFock.dGamma ContinuumL2Wavefunction1D
        (continuumL2Multiplication1D f) :=
  rfl

/-- On the one-particle sector, the second-quantized continuum charge density is exactly the
charge-scaled canonical bounded multiplication operator. -/
theorem continuumL2ChargeDensity1D_oneParticle
    (q : ℂ) (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    continuumL2ChargeDensity1D q f
        (AlgebraicFock.oneParticle ContinuumL2Wavefunction1D ψ) =
      AlgebraicFock.oneParticle ContinuumL2Wavefunction1D
        (q • L2MultiplicationRealLine.multiplicationOperator f ψ) := by
  rw [continuumL2ChargeDensity1D_apply]
  simp only [LinearMap.smul_apply, AlgebraicFock.dGamma_oneParticle]
  rw [← map_smul]
  rfl

/-- For a real bounded test function and real charge, the one-particle restriction is the same
charge-scaled real multiplication operator used by the analytic `L²` density expectation theorem. -/
theorem continuumL2ChargeDensity1D_oneParticle_real
    (q : ℝ) (test : ℝ → ℝ)
    (htest : MemLp (fun x => (test x : ℂ)) ∞ (volume : Measure ℝ))
    (ψ : ContinuumL2Wavefunction1D) :
    continuumL2ChargeDensity1D (q : ℂ)
        (L2MultiplicationRealLine.realMultiplier test htest)
        (AlgebraicFock.oneParticle ContinuumL2Wavefunction1D ψ) =
      AlgebraicFock.oneParticle ContinuumL2Wavefunction1D
        (((q : ℂ) • L2MultiplicationRealLine.multiplicationOperator
          (L2MultiplicationRealLine.realMultiplier test htest)) ψ) := by
  simpa using
    continuumL2ChargeDensity1D_oneParticle (q : ℂ)
      (L2MultiplicationRealLine.realMultiplier test htest) ψ

end
end Field
end Fermionic
end SecondQuantization
