import LeanCondensedMatter.Analysis.Operator.L2Multiplication
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity

set_option linter.style.header false

/-!
# Fermionic charge density from bounded `L²` multiplication

This module connects the basis-independent smeared fermionic charge-density interface to the
canonical bounded multiplication operators on complex `L²(μ)` supplied by the analysis layer.

For any measure `μ`, the smearing space is `L∞(μ, ℂ)`. Its canonical multiplication family is
complex-linear and may therefore be fed directly into `chargeDensity`, giving

```text
ρ_q(f) = q dΓ(M_f).
```

On the one-particle sector this acts exactly as the bounded analytic operator `q M_f`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Fermionic charge density induced by canonical bounded multiplication on complex `L²(μ)`. -/
noncomputable def l2ChargeDensity (μ : Measure α) (q : ℂ) :
    L2Multiplication.ComplexLInf μ →ₗ[ℂ]
      (AlgebraicFock (L2Multiplication.ComplexL2 μ) →ₗ[ℂ]
        AlgebraicFock (L2Multiplication.ComplexL2 μ)) :=
  chargeDensity (L2Multiplication.ComplexL2 μ) q
    (L2Multiplication.multiplicationLinear μ)

@[simp]
theorem l2ChargeDensity_apply
    (μ : Measure α) (q : ℂ) (f : L2Multiplication.ComplexLInf μ) :
    l2ChargeDensity μ q f =
      q • AlgebraicFock.dGamma (L2Multiplication.ComplexL2 μ)
        (L2Multiplication.multiplicationOperator μ f).toLinearMap :=
  rfl

/-- On the one-particle sector, the second-quantized `L²` charge density is exactly the
charge-scaled canonical bounded multiplication operator. -/
theorem l2ChargeDensity_oneParticle
    (μ : Measure α) (q : ℂ) (f : L2Multiplication.ComplexLInf μ)
    (ψ : L2Multiplication.ComplexL2 μ) :
    l2ChargeDensity μ q f
        (AlgebraicFock.oneParticle (L2Multiplication.ComplexL2 μ) ψ) =
      AlgebraicFock.oneParticle (L2Multiplication.ComplexL2 μ)
        (q • L2Multiplication.multiplicationOperator μ f ψ) := by
  rw [l2ChargeDensity_apply]
  simp only [LinearMap.smul_apply, AlgebraicFock.dGamma_oneParticle]
  rw [← map_smul]
  rfl

end
end Field
end Fermionic
end SecondQuantization
