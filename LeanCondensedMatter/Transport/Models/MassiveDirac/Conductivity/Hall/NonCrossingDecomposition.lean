import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.NonCrossing
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Non-crossing Hall decomposition benchmark

This module records the closed-form decomposition of the completed massive-Dirac non-crossing Hall
benchmark into the three terms written by Ado et al., EPL 111, 37004 (2015), Eq. (12a-c). The
existing occupation-derived clean intrinsic conductivity supplies the first term.

These are theorem-level benchmark identities only. In particular, this file does not introduce
primitive side-jump or skew-scattering definitions and does not classify an upstream ladder term by
mechanism name. Those identifications require separate provenance theorems from the concrete
non-crossing derivation.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- The existing clean intrinsic conductivity is exactly the first term of the Ado et al.
non-crossing decomposition, Eq. (12a). -/
theorem intrinsicHallConductivity_eq_ado_eq12a
    (e hbar m probeEnergy : ℝ) (hhbar : hbar ≠ 0) (hprobe : probeEnergy ≠ 0) :
    intrinsicHallConductivity e hbar m probeEnergy =
      -(e ^ 2 / planckFromReduced hbar) * (m / (2 * probeEnergy)) := by
  rw [intrinsicHallConductivity_eq_massiveDirac]
  unfold planckFromReduced
  field_simp [hhbar, hprobe, Real.pi_ne_zero]
  ring

/-- The completed non-crossing Hall benchmark equals the sum of the three closed expressions in
Ado et al., Eq. (12a-c). This is an algebraic regression target; it does not by itself identify the
second and third terms with particular upstream ladder contributions. -/
theorem nonCrossingHallConductivity_eq_ado_eq12_sum
    (e hbar m probeEnergy : ℝ) (hhbar : hbar ≠ 0) (hprobe : probeEnergy ≠ 0) :
    nonCrossingHallConductivity e hbar m probeEnergy =
      intrinsicHallConductivity e hbar m probeEnergy +
        (-(e ^ 2 / planckFromReduced hbar) *
          (2 * m * (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2)))) +
        (-(e ^ 2 / planckFromReduced hbar) *
          (3 * m * (probeEnergy ^ 2 - m ^ 2) ^ 2 /
            (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2))) := by
  have hprobeSq : 0 < probeEnergy ^ 2 := sq_pos_of_ne_zero hprobe
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg m]
  rw [intrinsicHallConductivity_eq_massiveDirac]
  unfold nonCrossingHallConductivity planckFromReduced
  field_simp [hhbar, hprobe, hden, Real.pi_ne_zero]
  ring

/-- After removing the already-isolated clean intrinsic contribution, the remaining non-crossing
benchmark is exactly the sum of Ado et al. Eq. (12b-c). The two terms remain benchmark targets here;
mechanism provenance is deliberately left to downstream classification theorems. -/
theorem nonCrossingHallConductivity_sub_intrinsicHallConductivity_eq_ado_eq12bc
    (e hbar m probeEnergy : ℝ) (hhbar : hbar ≠ 0) (hprobe : probeEnergy ≠ 0) :
    nonCrossingHallConductivity e hbar m probeEnergy -
        intrinsicHallConductivity e hbar m probeEnergy =
      (-(e ^ 2 / planckFromReduced hbar) *
        (2 * m * (probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2)))) +
      (-(e ^ 2 / planckFromReduced hbar) *
        (3 * m * (probeEnergy ^ 2 - m ^ 2) ^ 2 /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2))) := by
  rw [nonCrossingHallConductivity_eq_ado_eq12_sum e hbar m probeEnergy hhbar hprobe]
  ring

end

end QuantumTheory.Transport.Models.MassiveDirac
