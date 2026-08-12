import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Pure-point occupation interpolation

The finite Kubo–Bastin response is expressed using discrete pure-point probabilities `pₘ`. A
continuous-energy Středa representation instead needs a differentiable occupation function `f`.
This module records the statistics-independent bridge between the two descriptions: `f` agrees
with the supplied probabilities on the energy spectrum, and every transition difference is the
oriented integral of `f'` between the two energies.

No finite-lattice, fermionic Fock-space, contact, conductivity, or limiting statement occurs here.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory QuantumTheory.LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
variable (system : BoundedFreeSystem H)

/-- A differentiable complex occupation function reproducing the discrete pure-point probabilities
on every supplied energy eigenvalue. -/
structure PurePointOccupationInterpolation
    (data : PurePointLehmannData system ι) where
  /-- The continuous-energy occupation used by the later Bastin integral. -/
  occupation : ℝ → ℂ
  /-- The energy derivative of the occupation. -/
  occupationDerivative : ℝ → ℂ
  /-- The continuous occupation reproduces every discrete spectral probability. -/
  occupation_matches_probability :
    ∀ i, occupation (data.energy i) = (data.probability i : ℂ)
  /-- Pointwise differentiability, kept stronger than necessary for the first finite bridge. -/
  occupation_hasDerivAt :
    ∀ energy, HasDerivAt occupation (occupationDerivative energy) energy
  /-- The derivative is integrable on every oriented transition-energy interval. -/
  occupationDerivative_intervalIntegrable :
    ∀ m n, IntervalIntegrable occupationDerivative volume
      (data.energy n) (data.energy m)

/-- The occupation difference of two energy eigenstates is the oriented integral of the
occupation derivative between their energies. -/
theorem PurePointOccupationInterpolation.probability_sub_eq_integral
    {data : PurePointLehmannData system ι}
    (interpolation : PurePointOccupationInterpolation system data)
    (m n : ι) :
    (data.probability m : ℂ) - (data.probability n : ℂ) =
      ∫ energy in data.energy n..data.energy m,
        interpolation.occupationDerivative energy := by
  rw [← interpolation.occupation_matches_probability m,
    ← interpolation.occupation_matches_probability n]
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun energy _ => interpolation.occupation_hasDerivAt energy)
    (interpolation.occupationDerivative_intervalIntegrable m n)

/-- The same transition identity in the casted real-difference form used by the Lehmann weight. -/
theorem PurePointOccupationInterpolation.probabilityDifference_eq_integral
    {data : PurePointLehmannData system ι}
    (interpolation : PurePointOccupationInterpolation system data)
    (m n : ι) :
    (((data.probability m - data.probability n : ℝ) : ℂ)) =
      ∫ energy in data.energy n..data.energy m,
        interpolation.occupationDerivative energy := by
  simpa using interpolation.probability_sub_eq_integral system m n

end
end Transport
end QuantumTheory
