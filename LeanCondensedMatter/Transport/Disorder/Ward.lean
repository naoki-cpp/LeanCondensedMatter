import LeanCondensedMatter.Transport.Disorder.Ladder
import LeanCondensedMatter.Transport.Disorder.SCBA
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite SCBA charge-vertex Ward consistency

This module connects the supplied finite SCBA one-particle identities to the generic
retarded-advanced ladder without introducing an SCBA-specific ladder API.

A bounded charge vertex `Q` is conserved when it commutes with the clean Hamiltonian and every
finite-ensemble impurity potential. The impurity condition implies the left/right equivariance of
the canonical second moment proved in `Transport.Disorder.Moments`. With the same `C₂` in the
SCBA self-energy and generic RA ladder, the SCBA inverse relations then produce a ladder fixed point
whose resummation satisfies the finite Ward-consistency insertion

```text
Ḡᴿ Γ_Q Ḡᴬ = Ḡᴿ Q - Q Ḡᴬ.
```

The theorem is conditional on `IsUnit (1 - L_RA)`, exactly as in the generic ladder resummation.
No nonlinear SCBA existence theorem, electromagnetic Ward--Takahashi identity, conductivity
formula, crossed-diagram correction, or limiting procedure is asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

/-- Minimal bounded charge symmetry for a finite disorder ensemble. The charge vertex commutes with
both the clean Hamiltonian and every impurity potential; no conservation property is hidden in the
ladder definition itself. -/
structure ChargeSymmetry
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (charge : H →L[ℂ] H) : Prop where
  baseHamiltonian_commute : Commute ensemble.baseHamiltonian.1 charge
  impurityPotential_commute :
    ∀ ω, Commute (ensemble.impurityPotential ω).1 charge

namespace FiniteSCBASolution

variable {ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)}
variable {energy broadening : ℝ}
variable (solution : FiniteSCBASolution ensemble energy broadening)

/-- Finite SCBA/RA charge-vertex Ward consistency. Under explicit charge symmetry and the same
conditional ladder invertibility used by the generic resummation, inserting the resummed charge
vertex between the SCBA retarded and advanced Green operators gives the conserved-charge resolvent
difference. For `Q = 1`, the right-hand side is `Ḡᴿ - Ḡᴬ`.

The bare RA charge source is written as
`Q zᴬ - zᴿ Q` in the bounded-operator algebra so the theorem does not require a separate
SCBA-specific vertex definition. -/
theorem resummedLadderVertex_charge_ward_consistency
    (charge : H →L[ℂ] H)
    (symmetry : ChargeSymmetry ensemble charge)
    (hinvertible :
      IsUnit
        (1 - ensemble.retardedAdvancedLadderCLM
          (solution.green .retarded) (solution.green .advanced))) :
    solution.green .retarded *
        resummedLadderVertex
          (ensemble.retardedAdvancedLadderCLM
            (solution.green .retarded) (solution.green .advanced))
          hinvertible
          (charge * algebraMap ℂ (H →L[ℂ] H)
              (spectralParameter .advanced energy broadening) -
            algebraMap ℂ (H →L[ℂ] H)
              (spectralParameter .retarded energy broadening) * charge) *
        solution.green .advanced =
      solution.green .retarded * charge -
        charge * solution.green .advanced := by
  let ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    ensemble.retardedAdvancedLadderCLM
      (solution.green .retarded) (solution.green .advanced)
  let bare : H →L[ℂ] H :=
    charge * algebraMap ℂ (H →L[ℂ] H)
        (spectralParameter .advanced energy broadening) -
      algebraMap ℂ (H →L[ℂ] H)
        (spectralParameter .retarded energy broadening) * charge
  let dressed : H →L[ℂ] H :=
    bare +
      solution.selfEnergy .retarded * charge -
      charge * solution.selfEnergy .advanced

  change solution.green .retarded *
      resummedLadderVertex ladder hinvertible bare *
        solution.green .advanced =
    solution.green .retarded * charge -
      charge * solution.green .advanced

  have hshift :
      charge *
          ensemble.scbaShift .advanced energy broadening
            (solution.selfEnergy .advanced) -
        ensemble.scbaShift .retarded energy broadening
            (solution.selfEnergy .retarded) * charge =
      dressed := by
    dsimp [dressed, bare]
    unfold FiniteDisorderEnsemble.scbaShift
    rw [symmetry.baseHamiltonian_commute.eq]
    noncomm_ring

  have hinsertion :
      solution.green .retarded * dressed * solution.green .advanced =
        solution.green .retarded * charge -
          charge * solution.green .advanced := by
    rw [← hshift]
    calc
      solution.green .retarded *
          (charge *
              ensemble.scbaShift .advanced energy broadening
                (solution.selfEnergy .advanced) -
            ensemble.scbaShift .retarded energy broadening
                (solution.selfEnergy .retarded) * charge) *
          solution.green .advanced =
        solution.green .retarded * charge *
            (ensemble.scbaShift .advanced energy broadening
              (solution.selfEnergy .advanced) * solution.green .advanced) -
          (solution.green .retarded *
            ensemble.scbaShift .retarded energy broadening
              (solution.selfEnergy .retarded)) *
            charge * solution.green .advanced := by
              noncomm_ring
      _ = solution.green .retarded * charge -
          charge * solution.green .advanced := by
            rw [solution.shift_mul_green .advanced,
              solution.green_mul_shift .retarded]
            simp

  have hfixed : dressed = bare + ladder dressed := by
    change dressed = bare +
      ensemble.exactSecondMoment
        (solution.green .retarded * dressed * solution.green .advanced)
    rw [hinsertion, ensemble.exactSecondMoment_sub]
    rw [← ensemble.exactSecondMoment_mul_of_commutes
      (solution.green .retarded) charge symmetry.impurityPotential_commute]
    rw [← ensemble.mul_exactSecondMoment_of_commutes
      charge (solution.green .advanced) symmetry.impurityPotential_commute]
    rw [← solution.selfEnergy_eq_secondMoment .retarded,
      ← solution.selfEnergy_eq_secondMoment .advanced]
    dsimp [dressed]
    noncomm_ring

  have hunique :
      dressed = resummedLadderVertex ladder hinvertible bare :=
    eq_resummedLadderVertex_of_fixedPoint
      ladder hinvertible bare dressed hfixed
  rw [← hunique]
  exact hinsertion

end FiniteSCBASolution

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
