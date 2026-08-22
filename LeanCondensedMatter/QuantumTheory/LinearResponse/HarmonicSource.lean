import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticSwitching

set_option linter.style.header false

/-!
# Real quadratures of the adiabatic harmonic source

The canonical complex adiabatic phase can be decomposed into two real source profiles at a fixed
observation time `T`:

```text
f_cos(s) = Re exp ((iω - η) (T - s)),
f_sin(s) = Im exp ((iω - η) (T - s)).
```

These definitions are representation independent. They do not depend on particle statistics,
Fock-space realizations, current operators, lattice geometry, or conductivity normalization.
Concrete response theorems using these real source profiles belong in downstream realizations.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

/-- Real cosine quadrature of the normalized adiabatic harmonic source. -/
def adiabaticCosineSource (ω η T s : ℝ) : ℝ :=
  (adiabaticFrequencyPhase ω η (T - s)).re

/-- Real sine quadrature of the normalized adiabatic harmonic source. -/
def adiabaticSineSource (ω η T s : ℝ) : ℝ :=
  (adiabaticFrequencyPhase ω η (T - s)).im

/-- The canonical complex adiabatic phase is the complexification of its two real quadratures. -/
theorem adiabaticFrequencyPhase_eq_cosine_add_I_sine
    (ω η T s : ℝ) :
    adiabaticFrequencyPhase ω η (T - s) =
      (adiabaticCosineSource ω η T s : ℂ) +
        Complex.I * (adiabaticSineSource ω η T s : ℂ) := by
  apply Complex.ext <;>
    simp [adiabaticCosineSource, adiabaticSineSource]

@[simp]
theorem adiabaticCosineSource_at_observation (ω η T : ℝ) :
    adiabaticCosineSource ω η T T = 1 := by
  simp [adiabaticCosineSource]

@[simp]
theorem adiabaticSineSource_at_observation (ω η T : ℝ) :
    adiabaticSineSource ω η T T = 0 := by
  simp [adiabaticSineSource]

end
end LinearResponse
end QuantumTheory
