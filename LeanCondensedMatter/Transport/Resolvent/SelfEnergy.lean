import LeanCondensedMatter.Transport.Resolvent.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Abstract Dyson self-energy

This module isolates the model-independent algebraic meaning of a self-energy from any particular
Born, self-consistent Born, interaction, or disorder construction.

At a fixed spectral parameter, `IsSelfEnergy G₀ G Σ` means that the dressed Green operator satisfies
the left Dyson equation

```text
G = G₀ + G₀ Σ G.
```

This relation does not require inverses in its definition. When compatible inverses are available,
it recovers the conventional identity `Σ = G₀⁻¹ - G⁻¹`. Approximation schemes may construct
candidate self-energies without thereby asserting that a separately truncated Green approximation
satisfies the exact Dyson relation.
-/

namespace QuantumTheory
namespace Transport

section

variable {A : Type*} [Ring A]

/-- `selfEnergy` is a self-energy relating `freeGreen` and `dressedGreen` when the left Dyson
relation `G = G₀ + G₀ Σ G` holds. -/
def IsSelfEnergy (freeGreen dressedGreen selfEnergy : A) : Prop :=
  dressedGreen = freeGreen + freeGreen * selfEnergy * dressedGreen

namespace IsSelfEnergy

/-- A Dyson self-energy follows from inverse equations for the free and dressed shifts together
with `freeShift = dressedShift + selfEnergy`. -/
theorem of_shift
    {freeGreen dressedGreen selfEnergy freeShift dressedShift : A}
    (hfree : freeGreen * freeShift = 1)
    (hdressed : dressedShift * dressedGreen = 1)
    (hshift : freeShift = dressedShift + selfEnergy) :
    IsSelfEnergy freeGreen dressedGreen selfEnergy := by
  unfold IsSelfEnergy
  calc
    dressedGreen = (freeGreen * freeShift) * dressedGreen := by
      rw [hfree, one_mul]
    _ = freeGreen * (dressedShift + selfEnergy) * dressedGreen := by
      rw [hshift]
    _ = freeGreen * (dressedShift * dressedGreen) +
        freeGreen * selfEnergy * dressedGreen := by
      noncomm_ring
    _ = freeGreen + freeGreen * selfEnergy * dressedGreen := by
      rw [hdressed]
      simp

/-- With a left inverse of the free Green operator and a right inverse of the dressed Green
operator, the Dyson relation implies the conventional inverse-difference formula
`Σ = G₀⁻¹ - G⁻¹`. -/
theorem eq_inverse_sub_inverse
    {freeGreen dressedGreen selfEnergy freeInverse dressedInverse : A}
    (hself : IsSelfEnergy freeGreen dressedGreen selfEnergy)
    (hfree : freeInverse * freeGreen = 1)
    (hdressed : dressedGreen * dressedInverse = 1) :
    selfEnergy = freeInverse - dressedInverse := by
  have hinverse : freeInverse = dressedInverse + selfEnergy := by
    calc
      freeInverse = freeInverse * dressedGreen * dressedInverse := by
        rw [mul_assoc, hdressed, mul_one]
      _ = freeInverse *
          (freeGreen + freeGreen * selfEnergy * dressedGreen) * dressedInverse := by
        rw [hself]
      _ = (freeInverse * freeGreen) * dressedInverse +
          (freeInverse * freeGreen) * selfEnergy * (dressedGreen * dressedInverse) := by
        noncomm_ring
      _ = dressedInverse + selfEnergy := by
        rw [hfree, hdressed]
        simp
  calc
    selfEnergy = (dressedInverse + selfEnergy) - dressedInverse := by
      noncomm_ring
    _ = freeInverse - dressedInverse := by
      rw [← hinverse]

/-- Conversely, an inverse-difference self-energy satisfies the Dyson relation when the free inverse
is a right inverse and the dressed inverse is a left inverse. -/
theorem of_inverse_sub_inverse
    {freeGreen dressedGreen selfEnergy freeInverse dressedInverse : A}
    (hself : selfEnergy = freeInverse - dressedInverse)
    (hfree : freeGreen * freeInverse = 1)
    (hdressed : dressedInverse * dressedGreen = 1) :
    IsSelfEnergy freeGreen dressedGreen selfEnergy := by
  unfold IsSelfEnergy
  rw [hself]
  symm
  calc
    freeGreen + freeGreen * (freeInverse - dressedInverse) * dressedGreen =
        freeGreen + (freeGreen * freeInverse) * dressedGreen -
          freeGreen * (dressedInverse * dressedGreen) := by
      noncomm_ring
    _ = freeGreen + dressedGreen - freeGreen := by
      rw [hfree, hdressed]
      simp
    _ = dressedGreen := by
      noncomm_ring

/-- For two-sided inverses, the Dyson relation is equivalent to the inverse-difference definition of
self-energy. -/
theorem iff_eq_inverse_sub_inverse
    {freeGreen dressedGreen selfEnergy freeInverse dressedInverse : A}
    (hfreeLeft : freeInverse * freeGreen = 1)
    (hfreeRight : freeGreen * freeInverse = 1)
    (hdressedLeft : dressedInverse * dressedGreen = 1)
    (hdressedRight : dressedGreen * dressedInverse = 1) :
    IsSelfEnergy freeGreen dressedGreen selfEnergy ↔
      selfEnergy = freeInverse - dressedInverse := by
  constructor
  · intro hself
    exact hself.eq_inverse_sub_inverse hfreeLeft hdressedRight
  · intro hself
    exact of_inverse_sub_inverse hself hfreeRight hdressedLeft

end IsSelfEnergy

end

end Transport
end QuantumTheory
