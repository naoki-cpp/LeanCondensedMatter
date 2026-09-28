import LeanCondensedMatter.Analysis.Operator.L2Multiplication
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity

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

/-- The abstract fermionic charge density specialized to canonical bounded multiplication on
`L²(ℝ, ℂ)`. -/
noncomputable def continuumL2ChargeDensity1D (q : ℂ) :
    L2Multiplication.ComplexLInf (volume : Measure ℝ) →ₗ[ℂ]
      (AlgebraicFock (L2Multiplication.ComplexL2 (volume : Measure ℝ)) →ₗ[ℂ]
        AlgebraicFock (L2Multiplication.ComplexL2 (volume : Measure ℝ))) :=
  chargeDensity (L2Multiplication.ComplexL2 (volume : Measure ℝ)) q
    (L2Multiplication.multiplicationLinear (volume : Measure ℝ))

@[simp]
theorem continuumL2ChargeDensity1D_apply
    (q : ℂ) (f : L2Multiplication.ComplexLInf (volume : Measure ℝ)) :
    continuumL2ChargeDensity1D q f =
      q • AlgebraicFock.dGamma (L2Multiplication.ComplexL2 (volume : Measure ℝ))
        (L2Multiplication.multiplicationOperator (volume : Measure ℝ) f).toLinearMap :=
  rfl

/-- On the one-particle sector, the second-quantized continuum charge density is exactly the
charge-scaled canonical bounded multiplication operator. -/
theorem continuumL2ChargeDensity1D_oneParticle
    (q : ℂ) (f : L2Multiplication.ComplexLInf (volume : Measure ℝ))
    (ψ : L2Multiplication.ComplexL2 (volume : Measure ℝ)) :
    continuumL2ChargeDensity1D q f
        (AlgebraicFock.oneParticle (L2Multiplication.ComplexL2 (volume : Measure ℝ)) ψ) =
      AlgebraicFock.oneParticle (L2Multiplication.ComplexL2 (volume : Measure ℝ))
        (q • L2Multiplication.multiplicationOperator (volume : Measure ℝ) f ψ) := by
  rw [continuumL2ChargeDensity1D_apply]
  simp only [LinearMap.smul_apply, AlgebraicFock.dGamma_oneParticle]
  rw [← map_smul]
  rfl

end
end Field
end Fermionic
end SecondQuantization
