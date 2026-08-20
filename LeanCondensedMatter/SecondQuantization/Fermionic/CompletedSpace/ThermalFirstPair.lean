import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalKMS

set_option linter.style.header false

/-!
# Completed fermionic first-pair thermal reduction

This file combines the completed CAR peel identity with the completed free-Gibbs KMS rotation.
For an odd tail, the rotated term can be solved away with the one-mode Gibbs denominator
`1 + gβ(C)`.  The resulting scalar is exactly the normalized two-point Gibbs expectation.

The finite pairing induction remains in
`Common.Thermal.BlochDeDominicis.ExpectationPairingRecursion`; this file only supplies the
completed-representation thermal reduction data needed by that contract.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

namespace CompletedThermalLadder

/-- Completed free-Gibbs admissibility for an even ladder family.  At this stage the only local
condition needed to solve the fermionic KMS peel equation is the nonvanishing denominator
`1 + gβ(Cᵢ)`. -/
def completedFreeGibbsAdmissible (ε : Mode → ℝ) (β : ℝ) (n : ℕ)
    (C : Fin (2 * n) → CompletedThermalLadder Mode) : Prop :=
  ∀ i, (1 : ℂ) + (C i).gibbsFactor ε β ≠ 0

omit [LinearOrder Mode] in
/-- Completed Gibbs admissibility is stable under deleting the first ladder and one partner. -/
theorem completedFreeGibbsAdmissible_erase
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ)
    (C : Fin (2 * (n + 1)) → CompletedThermalLadder Mode)
    (hC : completedFreeGibbsAdmissible ε β (n + 1) C)
    (j : Fin (2 * n + 1)) :
    completedFreeGibbsAdmissible ε β n
      (fun i : Fin (2 * n) => C ((j.succAbove i).succ)) := by
  intro i
  exact hC _

/-- For an odd tail, completed CAR exchange followed by KMS rotation solves the wrapped term.
The coefficient `g / (1 + g)` is the Fermi thermal factor attached to the leading ladder. -/
theorem completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (n : ℕ) (C : CompletedThermalLadder Mode) (l : List (CompletedThermalLadder Mode))
    (hlen : l.length = 2 * n + 1)
    (hne : (1 : ℂ) + C.gibbsFactor ε β ≠ 0) :
    completedFreeGibbsExpectation ε β hsum (C :: l) =
      (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) *
        (purePointGibbsDensityOperator completedOccupationHilbertBasis
          (fermionEnergy ε) β hsum).expectation (thermalPeelSum C l) := by
  set E : ℂ := completedFreeGibbsExpectation ε β hsum (C :: l)
  set P : ℂ :=
    (purePointGibbsDensityOperator completedOccupationHilbertBasis
      (fermionEnergy ε) β hsum).expectation (thermalPeelSum C l)
  set R : ℂ := completedFreeGibbsExpectation ε β hsum (l ++ [C])
  have hpeel : E = P + ((-1 : ℂ) ^ l.length) * R := by
    simpa [E, P, R] using
      completedFreeGibbsExpectation_cons_eq_peel_add_rotated ε β hsum C l
  have hkms : E = C.gibbsFactor ε β * R := by
    simpa [E, R] using
      completedFreeGibbsExpectation_cons_eq_gibbsFactor_mul_rotate ε β hsum C l
  have hsign : ((-1 : ℂ) ^ l.length) = -1 := by
    rw [hlen]
    have hmod : (2 * n + 1) % 2 = 1 % 2 := by omega
    have h := Common.BlochDeDominicis.zetaInt_pow_eq_of_mod_two_eq
      Common.Statistics.fermion hmod
    simpa using h
  have hgr : C.gibbsFactor ε β * R = P - R := by
    calc
      C.gibbsFactor ε β * R = E := hkms.symm
      _ = P + ((-1 : ℂ) ^ l.length) * R := hpeel
      _ = P - R := by rw [hsign]; ring
  have hRmul : R * ((1 : ℂ) + C.gibbsFactor ε β) = P := by
    calc
      R * ((1 : ℂ) + C.gibbsFactor ε β) = C.gibbsFactor ε β * R + R := by ring
      _ = (P - R) + R := by rw [hgr]
      _ = P := by ring
  have hR : R = P / ((1 : ℂ) + C.gibbsFactor ε β) :=
    (eq_div_iff hne).2 hRmul
  calc
    completedFreeGibbsExpectation ε β hsum (C :: l) = E := rfl
    _ = C.gibbsFactor ε β * R := hkms
    _ = (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) * P := by
      rw [hR]
      ring
    _ = (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) *
        (purePointGibbsDensityOperator completedOccupationHilbertBasis
          (fermionEnergy ε) β hsum).expectation (thermalPeelSum C l) := rfl

/-- The normalized two-point completed Gibbs expectation is the scalar CAR coefficient multiplied
by the same Gibbs ratio that solves the odd-tail KMS equation. -/
theorem completedFreeGibbsExpectation_pair_eq
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (C D : CompletedThermalLadder Mode)
    (hne : (1 : ℂ) + C.gibbsFactor ε β ≠ 0) :
    completedFreeGibbsExpectation ε β hsum [C, D] =
      (C.gibbsFactor ε β / ((1 : ℂ) + C.gibbsFactor ε β)) *
        C.anticommutatorValue D := by
  have h := completedFreeGibbsExpectation_cons_eq_gibbsRatio_mul_peel
    ε β hsum 0 C [D] (by simp) hne
  have hpeel :
      (purePointGibbsDensityOperator completedOccupationHilbertBasis
        (fermionEnergy ε) β hsum).expectation (thermalPeelSum C [D]) =
        C.anticommutatorValue D := by
    simp [thermalPeelSum]
  rw [hpeel] at h
  exact h

end CompletedThermalLadder

end
end Fermionic
end SecondQuantization
