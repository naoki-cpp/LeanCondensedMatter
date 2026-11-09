import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBesselJ
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVSpectralConjugation

set_option linter.style.header false

/-!
# Bessel-J spectral-center UV Schwarz reflection

The complex spectral-center Bessel-J UV value inherits Schwarz reflection
from the canonical fixed-spectral Fourier UV conjugation theorem in
`RadialUVSpectralConjugation`. This uses the previously proved finite-cutoff
conjugation and UV-limit uniqueness; no independent duplicate Fourier
conjugation theorem, Hankel branch assumption, or outgoing-wave asymptotic
is introduced here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open scoped ComplexConjugate

/-- The canonical Bessel-J spectral-center UV value has the correct
retarded/advanced conjugation under the physical decomposition
`s = E²-M²`. This result uses the *proved* finite-integral
conjugation, not an independent Bessel-Y or Hankel postulate. -/
theorem massiveDiracRadialBesselJCenterUVValue_conj_of_energy_mass
    (v c : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    conj (massiveDiracRadialBesselJCenterUVValue
      v c (energy ^ 2 - mass ^ 2)) =
    massiveDiracRadialBesselJCenterUVValue
      v c (conj (energy ^ 2 - mass ^ 2)) := by
  calc
    conj (massiveDiracRadialBesselJCenterUVValue
      v c (energy ^ 2 - mass ^ 2)) =
        conj (massiveDiracRadialFourierUVValue v c energy mass) := by
      rw [massiveDiracRadialFourierUVValue_eq_besselJCenter]
    _ = massiveDiracRadialFourierUVValue
          v c (conj energy) (conj mass) :=
      massiveDiracRadialFourierUVValue_conj v c energy mass hv hc hcenter
    _ = massiveDiracRadialBesselJCenterUVValue
          v c ((conj energy) ^ 2 - (conj mass) ^ 2) :=
      massiveDiracRadialFourierUVValue_eq_besselJCenter
        v c (conj energy) (conj mass)
    _ = massiveDiracRadialBesselJCenterUVValue
          v c (conj (energy ^ 2 - mass ^ 2)) := by
      simp only [map_sub, map_pow]

end

end QuantumTheory.Models.MassiveDirac
