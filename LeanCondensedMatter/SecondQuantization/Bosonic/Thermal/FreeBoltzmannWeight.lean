import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# The free bosonic Boltzmann weight

This module defines the Gibbs weight `e^{-βE(n)}` for the free bosonic energy. Factorization into
one-mode weights and summability over all occupation states are proved in later modules.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- The free bosonic Boltzmann weight `e^{-βE(n)}`. -/
noncomputable def boltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℝ :=
  Real.exp (-β * freeEigenvalue ε n)

end Bosonic
end SecondQuantization
