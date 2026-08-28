import Mathlib.Tactic

set_option linter.style.header false

/-!
# Abstract Dyson self-energy

This module isolates the model-independent algebraic meaning of a self-energy from any particular
Born, self-consistent Born, interaction, or disorder construction.

At a fixed spectral parameter, `IsSelfEnergy G₀ G Σ` means that the dressed Green operator satisfies
both noncommutative Dyson orientations

```text
G = G₀ + G₀ Σ G,
G = G₀ + G Σ G₀.
```

Keeping both orientations in the abstract relation makes it stable under adjunction: the adjoint of
the left Dyson equation is the right Dyson equation for the adjointed data, and conversely. The
relation does not require inverses in its definition. When compatible two-sided inverses are
available, it recovers the conventional identity `Σ = G₀⁻¹ - G⁻¹`. Approximation schemes may
construct candidate self-energies without thereby asserting that a separately truncated Green
approximation satisfies the exact Dyson relation.
-/

namespace QuantumTheory
namespace Transport

section

variable {A : Type*} [Ring A]

/-- `selfEnergy` is a self-energy relating `freeGreen` and `dressedGreen` when both the left- and
right-oriented Dyson relations hold. -/
def IsSelfEnergy (freeGreen dressedGreen selfEnergy : A) : Prop :=
  dressedGreen = freeGreen + freeGreen * selfEnergy * dressedGreen ∧
    dressedGreen = freeGreen + dressedGreen * selfEnergy * freeGreen

namespace IsSelfEnergy

/-- The left-oriented Dyson equation carried by an abstract self-energy relation. -/
theorem leftDyson
    {freeGreen dressedGreen selfEnergy : A}
    (hself : IsSelfEnergy freeGreen dressedGreen selfEnergy) :
    dressedGreen = freeGreen + freeGreen * selfEnergy * dressedGreen :=
  hself.1

/-- The right-oriented Dyson equation carried by an abstract self-energy relation. -/
theorem rightDyson
    {freeGreen dressedGreen selfEnergy : A}
    (hself : IsSelfEnergy freeGreen dressedGreen selfEnergy) :
    dressedGreen = freeGreen + dressedGreen * selfEnergy * freeGreen :=
  hself.2

/-- The two-sided Dyson self-energy relation is preserved by adjunction. The two Dyson orientations
are exchanged because `star` reverses noncommutative multiplication order. -/
theorem star_closed
    [StarRing A]
    {freeGreen dressedGreen selfEnergy : A}
    (hself : IsSelfEnergy freeGreen dressedGreen selfEnergy) :
    IsSelfEnergy (star freeGreen) (star dressedGreen) (star selfEnergy) := by
  constructor
  · have h := congrArg (fun x : A => star x) hself.rightDyson
    simpa only [star_add, star_mul, star_star, mul_assoc] using h
  · have h := congrArg (fun x : A => star x) hself.leftDyson
    simpa only [star_add, star_mul, star_star, mul_assoc] using h

/-- A Dyson self-energy follows from two-sided inverse equations for the free and dressed shifts
together with `freeShift = dressedShift + selfEnergy`. -/
theorem of_shift
    {freeGreen dressedGreen selfEnergy freeShift dressedShift : A}
    (hfreeGreenShift : freeGreen * freeShift = 1)
    (hfreeShiftGreen : freeShift * freeGreen = 1)
    (hdressedShiftGreen : dressedShift * dressedGreen = 1)
    (hdressedGreenShift : dressedGreen * dressedShift = 1)
    (hshift : freeShift = dressedShift + selfEnergy) :
    IsSelfEnergy freeGreen dressedGreen selfEnergy := by
  constructor
  · calc
      dressedGreen = (freeGreen * freeShift) * dressedGreen := by
        rw [hfreeGreenShift, one_mul]
      _ = freeGreen * (dressedShift + selfEnergy) * dressedGreen := by
        rw [hshift]
      _ = freeGreen * (dressedShift * dressedGreen) +
          freeGreen * selfEnergy * dressedGreen := by
        noncomm_ring
      _ = freeGreen + freeGreen * selfEnergy * dressedGreen := by
        rw [hdressedShiftGreen]
        simp
  · calc
      dressedGreen = dressedGreen * (freeShift * freeGreen) := by
        rw [hfreeShiftGreen, mul_one]
      _ = dressedGreen * (dressedShift + selfEnergy) * freeGreen := by
        rw [hshift]
        noncomm_ring
      _ = (dressedGreen * dressedShift) * freeGreen +
          dressedGreen * selfEnergy * freeGreen := by
        noncomm_ring
      _ = freeGreen + dressedGreen * selfEnergy * freeGreen := by
        rw [hdressedGreenShift]
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
        exact congrArg (fun x : A => freeInverse * x * dressedInverse) hself.leftDyson
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

/-- Conversely, an inverse-difference self-energy satisfies both Dyson orientations when the free
and dressed Green operators have the supplied two-sided inverses. -/
theorem of_inverse_sub_inverse
    {freeGreen dressedGreen selfEnergy freeInverse dressedInverse : A}
    (hself : selfEnergy = freeInverse - dressedInverse)
    (hfreeLeft : freeInverse * freeGreen = 1)
    (hfreeRight : freeGreen * freeInverse = 1)
    (hdressedLeft : dressedInverse * dressedGreen = 1)
    (hdressedRight : dressedGreen * dressedInverse = 1) :
    IsSelfEnergy freeGreen dressedGreen selfEnergy := by
  constructor
  · rw [hself]
    symm
    calc
      freeGreen + freeGreen * (freeInverse - dressedInverse) * dressedGreen =
          freeGreen + (freeGreen * freeInverse) * dressedGreen -
            freeGreen * (dressedInverse * dressedGreen) := by
        noncomm_ring
      _ = freeGreen + dressedGreen - freeGreen := by
        rw [hfreeRight, hdressedLeft]
        simp
      _ = dressedGreen := by
        noncomm_ring
  · rw [hself]
    symm
    calc
      freeGreen + dressedGreen * (freeInverse - dressedInverse) * freeGreen =
          freeGreen + dressedGreen * (freeInverse * freeGreen) -
            (dressedGreen * dressedInverse) * freeGreen := by
        noncomm_ring
      _ = freeGreen + dressedGreen - freeGreen := by
        rw [hfreeLeft, hdressedRight]
        simp
      _ = dressedGreen := by
        noncomm_ring

/-- For two-sided inverses, the two-sided Dyson relation is equivalent to the inverse-difference
definition of self-energy. -/
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
    exact of_inverse_sub_inverse hself hfreeLeft hfreeRight hdressedLeft hdressedRight

end IsSelfEnergy

end

end Transport
end QuantumTheory
