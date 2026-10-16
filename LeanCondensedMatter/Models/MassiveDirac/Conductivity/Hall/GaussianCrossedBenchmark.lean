import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.NonCrossingMechanismClassification
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Gaussian crossed Hall benchmark identities

These closed-form algebraic identities express the Ado et al., EPL 111, 37004
(2015) massive-Dirac Hall benchmark in terms of its non-crossing, crossed X,
and intrinsic/side-jump/skew parts. They are independent of the finite-cutoff
regulated X/Psi real-space integrals and do not prove any regulator limit.

**Source notation caveat:** in the arXiv v3 PDF of Ado et al., Eq. (18)
appears without the factor `m` in the skew numerator. The expression below
is the one *algebraically implied* by the preceding Eq. (12c) and Eq. (17),
including that factor. It is odd under reversal of the Dirac mass, as
expected for the Hall response. This module therefore does not assert
literal transcription of the displayed Eq. (18) as printed.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- The exact closed-form crossed correction required to turn the proved non-crossing Ado result
into the full Gaussian-disorder Ado benchmark.

This is an algebraic *target identity*, not an evaluation of either crossed trace integral:
the finite-regulator `X` and `Psi` kernels still require their own analytical limits. The
correction on the left is the required sum of those contributions after taking those limits.
In particular, the statement does not assert `Psi = 0` or identify an unevaluated crossed
integral with this expression. -/
theorem nonCrossingHallConductivity_add_gaussianCrossedTarget_eq_gaussianBenchmark
    (e hbar m probeEnergy : ℝ) :
    nonCrossingHallConductivity e hbar m probeEnergy +
        (4 * e ^ 2 / planckFromReduced hbar) *
          (probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) =
      -(8 * e ^ 2 / planckFromReduced hbar) *
        (probeEnergy * m ^ 3 /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) := by
  unfold nonCrossingHallConductivity
  ring


/-- The full Gaussian skew-scattering benchmark **inferred from** Ado et al., EPL 111,
37004 (2015), Eqs. (12c) and (17): the non-crossing skew term plus the crossed X target.
The derived numerator contains `m`; see the source-notation caveat above. The Psi contribution vanishes
only at the evaluated massive-Dirac benchmark level.

This is an algebraic identity between the quoted closed expressions.
In particular, it does **not** establish that the regulated X/Psi
real-space integrals converge to those expressions. -/
theorem adoEq18SkewBenchmark_eq_nonCrossingSkew_add_crossedTarget
    (e hbar m probeEnergy : ℝ) (hprobe : probeEnergy ≠ 0) :
    (e ^ 2 / planckFromReduced hbar) *
        (m * (probeEnergy ^ 2 - m ^ 2) * (5 * probeEnergy ^ 2 + 3 * m ^ 2) /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2)) =
      -(e ^ 2 / planckFromReduced hbar) *
          (3 * m * (probeEnergy ^ 2 - m ^ 2) ^ 2 /
            (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2)) +
        (4 * e ^ 2 / planckFromReduced hbar) *
          (probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) := by
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    have hsq : 0 < probeEnergy ^ 2 := sq_pos_of_ne_zero hprobe
    nlinarith [sq_nonneg m]
  have hfrac :
      m * (probeEnergy ^ 2 - m ^ 2) * (5 * probeEnergy ^ 2 + 3 * m ^ 2) /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) =
        -(3 * m * (probeEnergy ^ 2 - m ^ 2) ^ 2 /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2)) +
        4 * probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 := by
    field_simp [hprobe, hden]
    ring
  rw [hfrac]
  ring

/-- The full Gaussian-disorder Hall *benchmark* is the Ado intrinsic
Eq. (12a) plus side-jump Eq. (12b) plus full skew Eq. (18) sum.

This combines algebraic benchmark identities, not the unproved
regulated-X/Psi-integral evaluation or an independent microscopic
side-jump scattering derivation. -/
theorem intrinsic_sideJumpType_adoEq18SkewBenchmark_sum_eq_gaussianBenchmark
    (e hbar m probeEnergy : ℝ) (hhbar : hbar ≠ 0)
    (hprobe : probeEnergy ≠ 0) :
    intrinsicHallConductivity e hbar m probeEnergy +
        (-(e ^ 2 / planckFromReduced hbar) *
          (2 * m * (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2)))) +
        (e ^ 2 / planckFromReduced hbar) *
          (m * (probeEnergy ^ 2 - m ^ 2) *
            (5 * probeEnergy ^ 2 + 3 * m ^ 2) /
            (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2)) =
      -(8 * e ^ 2 / planckFromReduced hbar) *
        (probeEnergy * m ^ 3 /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) := by
  rw [adoEq18SkewBenchmark_eq_nonCrossingSkew_add_crossedTarget
    e hbar m probeEnergy hprobe]
  rw [← nonCrossingHallConductivity_add_gaussianCrossedTarget_eq_gaussianBenchmark]
  have hnc :=
    intrinsic_sideJumpType_nonCrossingSkewType_sum_eq_nonCrossingHallConductivity
      e hbar m probeEnergy hhbar hprobe
  dsimp at hnc
  rw [← hnc]
  ring


/-- The full Gaussian Hall benchmark is odd under mass reversal.

Unlike a bare transcription of the displayed arXiv-v3 Eq. (18), the
reconstructed mechanism sum obeys the expected mass-reversal parity. -/
theorem gaussianHallBenchmark_neg_mass
    (e hbar m probeEnergy : ℝ) :
    -(8 * e ^ 2 / planckFromReduced hbar) *
        (probeEnergy * (-m) ^ 3 /
          (probeEnergy ^ 2 + 3 * (-m) ^ 2) ^ 2) =
      - (-(8 * e ^ 2 / planckFromReduced hbar) *
        (probeEnergy * m ^ 3 /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2)) := by
  ring

/-- The corrected skew-scattering benchmark inferred from Eqs. (12c) and (17)
is odd under mass reversal. -/
theorem adoEq18SkewBenchmark_neg_mass
    (e hbar m probeEnergy : ℝ) :
    (e ^ 2 / planckFromReduced hbar) *
        ((-m) * (probeEnergy ^ 2 - (-m) ^ 2) *
          (5 * probeEnergy ^ 2 + 3 * (-m) ^ 2) /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * (-m) ^ 2) ^ 2)) =
      - ((e ^ 2 / planckFromReduced hbar) *
        (m * (probeEnergy ^ 2 - m ^ 2) *
          (5 * probeEnergy ^ 2 + 3 * m ^ 2) /
          (2 * probeEnergy * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2))) := by
  ring

end

end QuantumTheory.Models.MassiveDirac
