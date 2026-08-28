import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Single-particle decay width and lifetime

This module keeps the lifetime extracted from a retarded one-particle self-energy distinct from the
transport lifetime used by relaxation-time conductivity benchmarks.  For a retarded self-energy
`Σᴿ`, the decay half-width is represented by

```text
Γ_q = -Im Σᴿ,
```

and the corresponding single-particle lifetime convention is

```text
τ_q = ℏ / (2 Γ_q).
```

The definitions are total as real-valued expressions.  Positivity is exposed separately, so a
model-specific disorder calculation must prove the sign of its retarded self-energy before it can
construct a positive lifetime.  No identification with a transport lifetime is made here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Single-particle decay half-width extracted from a retarded self-energy, `Γ_q = -Im Σᴿ`. -/
def retardedSelfEnergyDecayWidth (retardedSelfEnergy : ℂ) : ℝ :=
  -retardedSelfEnergy.im

/-- Positive single-particle lifetime `τ_q`, deliberately distinct from a transport lifetime. -/
structure PositiveSingleParticleLifetime where
  /-- Single-particle lifetime. -/
  lifetime : ℝ
  lifetime_pos : 0 < lifetime

/-- Lifetime associated with a decay half-width in the convention `τ_q = ℏ/(2Γ_q)`. -/
def singleParticleLifetimeFromDecayWidth (hbar decayWidth : ℝ) : ℝ :=
  hbar / (2 * decayWidth)

/-- Positive `ℏ` and positive decay width produce a positive single-particle lifetime. -/
def positiveSingleParticleLifetimeFromDecayWidth
    (hbar decayWidth : ℝ) (hhbar : 0 < hbar) (hdecayWidth : 0 < decayWidth) :
    PositiveSingleParticleLifetime :=
  ⟨singleParticleLifetimeFromDecayWidth hbar decayWidth,
    div_pos hhbar (mul_pos (by norm_num) hdecayWidth)⟩

@[simp]
theorem positiveSingleParticleLifetimeFromDecayWidth_lifetime
    (hbar decayWidth : ℝ) (hhbar : 0 < hbar) (hdecayWidth : 0 < decayWidth) :
    (positiveSingleParticleLifetimeFromDecayWidth
      hbar decayWidth hhbar hdecayWidth).lifetime =
      hbar / (2 * decayWidth) :=
  rfl

/-- A negative imaginary part of a retarded self-energy gives a positive decay width. -/
theorem retardedSelfEnergyDecayWidth_pos
    (retardedSelfEnergy : ℂ) (him : retardedSelfEnergy.im < 0) :
    0 < retardedSelfEnergyDecayWidth retardedSelfEnergy := by
  simpa [retardedSelfEnergyDecayWidth] using neg_pos.mpr him

end

end Transport
end QuantumTheory
