import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Relaxation-time inputs and self-energy decay width

This module keeps two physically distinct time scales separate.

- `PositiveTransportLifetime` is the current-relaxation time `τ_tr` used by phenomenological
  longitudinal transport formulas.
- `PositiveSingleParticleLifetime` is the spectral/quantum lifetime `τ_q` associated with a
  retarded self-energy width.

For a scalar retarded self-energy `Σᴿ`, the decay half-width is defined by

```text
Γ_q = -Im Σᴿ.
```

When `Γ_q > 0`, the lifetime convention used here is

```text
τ_q = ℏ / (2 Γ_q).
```

No equality between `τ_q` and `τ_tr` is asserted.  A downstream collision or vertex calculation
must supply any transport-lifetime relation.
-/

namespace QuantumTheory
namespace Transport

/-- Positive transport relaxation time `τ_tr`.  Unless a downstream theorem derives it from a
microscopic collision or vertex problem, this datum is an explicit phenomenological input. -/
structure PositiveTransportLifetime where
  /-- Transport relaxation time. -/
  lifetime : ℝ
  lifetime_pos : 0 < lifetime

/-- Positive single-particle (spectral/quantum) lifetime `τ_q`. -/
structure PositiveSingleParticleLifetime where
  /-- Single-particle lifetime. -/
  lifetime : ℝ
  lifetime_pos : 0 < lifetime

/-- Decay half-width associated with a scalar retarded self-energy,
`Γ_q = -Im Σᴿ`. -/
def retardedSelfEnergyDecayWidth (selfEnergy : ℂ) : ℝ :=
  -selfEnergy.im

@[simp] theorem retardedSelfEnergyDecayWidth_pos_iff (selfEnergy : ℂ) :
    0 < retardedSelfEnergyDecayWidth selfEnergy ↔ selfEnergy.im < 0 := by
  simp [retardedSelfEnergyDecayWidth]

/-- Convert a positive spectral half-width `Γ_q` to the corresponding single-particle lifetime
using `τ_q = ℏ/(2Γ_q)`. -/
noncomputable def singleParticleLifetimeOfDecayWidth
    (hbar decayWidth : ℝ) (hhbar : 0 < hbar) (hdecayWidth : 0 < decayWidth) :
    PositiveSingleParticleLifetime where
  lifetime := hbar / (2 * decayWidth)
  lifetime_pos := div_pos hhbar (mul_pos (by norm_num) hdecayWidth)

@[simp] theorem singleParticleLifetimeOfDecayWidth_lifetime
    (hbar decayWidth : ℝ) (hhbar : 0 < hbar) (hdecayWidth : 0 < decayWidth) :
    (singleParticleLifetimeOfDecayWidth hbar decayWidth hhbar hdecayWidth).lifetime =
      hbar / (2 * decayWidth) := rfl

/-- Extract a positive single-particle lifetime from a scalar retarded self-energy whose imaginary
part is strictly negative.  This is a spectral lifetime only; it is not a transport lifetime. -/
noncomputable def singleParticleLifetimeOfRetardedSelfEnergy
    (hbar : ℝ) (selfEnergy : ℂ) (hhbar : 0 < hbar) (hselfEnergy : selfEnergy.im < 0) :
    PositiveSingleParticleLifetime :=
  singleParticleLifetimeOfDecayWidth hbar (retardedSelfEnergyDecayWidth selfEnergy) hhbar
    ((retardedSelfEnergyDecayWidth_pos_iff selfEnergy).2 hselfEnergy)

@[simp] theorem singleParticleLifetimeOfRetardedSelfEnergy_lifetime
    (hbar : ℝ) (selfEnergy : ℂ) (hhbar : 0 < hbar) (hselfEnergy : selfEnergy.im < 0) :
    (singleParticleLifetimeOfRetardedSelfEnergy hbar selfEnergy hhbar hselfEnergy).lifetime =
      hbar / (2 * (-selfEnergy.im)) := by
  rfl

end Transport
end QuantumTheory
