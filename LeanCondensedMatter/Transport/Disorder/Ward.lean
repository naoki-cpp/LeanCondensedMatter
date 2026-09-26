import LeanCondensedMatter.Transport.Disorder.Ladder
import LeanCondensedMatter.Transport.Disorder.SCBA
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite SCBA charge-vertex Ward consistency

This module connects the supplied finite SCBA one-particle identities to the generic
retarded-advanced ladder without introducing an SCBA-specific ladder API.

The Ward bridge needs only a bounded charge vertex `Q` that commutes with the clean Hamiltonian
and for which the canonical second moment is equivariant on both sides. Pointwise commutation with
every finite-ensemble impurity potential is provided as a sufficient condition for that equivariance.
With the same `C₂` in the SCBA self-energy and generic RA ladder, the SCBA inverse relations then
give the finite Ward-consistency insertion

```text
(zᴬ - zᴿ) • (Ḡᴿ Γ_Q Ḡᴬ) = Ḡᴿ Q - Q Ḡᴬ,
```

where `Γ_Q = (I - L_RA)⁻¹ Q` is exactly the generic resummed ladder vertex with bare vertex `Q`.

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

/-- Minimal bounded charge-symmetry interface used by the finite Ward bridge. Besides commuting
with the clean Hamiltonian, the charge must act equivariantly on both sides of the canonical exact
second moment. Pointwise commutation with each impurity potential is a sufficient, but not required,
condition. -/
structure ChargeSymmetry
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (charge : H →L[ℂ] H) : Prop where
  baseHamiltonian_commute : Commute ensemble.baseHamiltonian.1 charge
  secondMoment_mul_charge :
    ∀ kernel,
      ensemble.exactSecondMoment kernel * charge =
        ensemble.exactSecondMoment (kernel * charge)
  charge_mul_secondMoment :
    ∀ kernel,
      charge * ensemble.exactSecondMoment kernel =
        ensemble.exactSecondMoment (charge * kernel)

/-- The identity operator is always a charge symmetry. This does not require scalar disorder:
identity commutes with every clean Hamiltonian, and left/right multiplication by identity leaves
the exact second-moment argument unchanged. -/
theorem ChargeSymmetry.one
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)) :
    ChargeSymmetry ensemble (1 : H →L[ℂ] H) := by
  refine
    { baseHamiltonian_commute := ?_
      secondMoment_mul_charge := ?_
      charge_mul_secondMoment := ?_ }
  · simp [Commute]
  · intro kernel
    simp
  · intro kernel
    simp

/-- Pointwise commutation of every impurity potential with the charge is sufficient for the
second-moment equivariance required by `ChargeSymmetry`. -/
theorem ChargeSymmetry.of_impurityPotential_commute
    {ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)}
    {charge : H →L[ℂ] H}
    (hbase : Commute ensemble.baseHamiltonian.1 charge)
    (himpurity : ∀ ω, Commute (ensemble.impurityPotential ω).1 charge) :
    ChargeSymmetry ensemble charge where
  baseHamiltonian_commute := hbase
  secondMoment_mul_charge := fun kernel =>
    ensemble.exactSecondMoment_mul_of_commutes kernel charge himpurity
  charge_mul_secondMoment := fun kernel =>
    ensemble.mul_exactSecondMoment_of_commutes charge kernel himpurity

namespace FiniteSCBASolution

variable {ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)}
variable {energy broadening : ℝ}
variable (solution : FiniteSCBASolution ensemble energy broadening)

/-- Finite SCBA/RA charge-vertex Ward consistency. Under the minimal charge-symmetry interface and
the same conditional ladder invertibility used by the generic resummation, the generic corrected
charge vertex `Γ_Q = (I - L_RA)⁻¹ Q` obeys

`(zᴬ - zᴿ) • (Ḡᴿ Γ_Q Ḡᴬ) = Ḡᴿ Q - Q Ḡᴬ`.

For `Q = 1`, the right-hand side is `Ḡᴿ - Ḡᴬ`. -/
theorem resummedLadderVertex_charge_ward_consistency
    (charge : H →L[ℂ] H)
    (symmetry : ChargeSymmetry ensemble charge)
    (hinvertible :
      IsUnit
        (1 - ensemble.retardedAdvancedLadderCLM
          (solution.green .retarded) (solution.green .advanced))) :
    (spectralParameter .advanced energy broadening -
        spectralParameter .retarded energy broadening) •
      (solution.green .retarded *
        resummedLadderVertex
          (ensemble.retardedAdvancedLadderCLM
            (solution.green .retarded) (solution.green .advanced))
          hinvertible
          charge *
        solution.green .advanced) =
      solution.green .retarded * charge -
        charge * solution.green .advanced := by
  let ladder : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    ensemble.retardedAdvancedLadderCLM
      (solution.green .retarded) (solution.green .advanced)
  let scale : ℂ :=
    spectralParameter .advanced energy broadening -
      spectralParameter .retarded energy broadening
  let bare : H →L[ℂ] H :=
    charge * algebraMap ℂ (H →L[ℂ] H)
        (spectralParameter .advanced energy broadening) -
      algebraMap ℂ (H →L[ℂ] H)
        (spectralParameter .retarded energy broadening) * charge
  let dressed : H →L[ℂ] H :=
    bare +
      solution.selfEnergy .retarded * charge -
      charge * solution.selfEnergy .advanced
  change scale •
      (solution.green .retarded *
        resummedLadderVertex ladder hinvertible charge *
          solution.green .advanced) =
    solution.green .retarded * charge -
      charge * solution.green .advanced
  have hbare : bare = scale • charge := by
    dsimp [bare, scale]
    rw [sub_smul]
    simp [Algebra.algebraMap_eq_smul_one]
  have hshift :
      charge *
          ensemble.scbaShift .advanced energy broadening
            (solution.selfEnergy .advanced) -
        ensemble.scbaShift .retarded energy broadening
            (solution.selfEnergy .retarded) * charge =
      dressed := by
    dsimp [dressed, bare]
    unfold FiniteDisorderEnsemble.scbaShift
    simp only [mul_sub, sub_mul]
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
    rw [← symmetry.secondMoment_mul_charge (solution.green .retarded)]
    rw [← symmetry.charge_mul_secondMoment (solution.green .advanced)]
    rw [← solution.selfEnergy_eq_secondMoment .retarded,
      ← solution.selfEnergy_eq_secondMoment .advanced]
    dsimp [dressed]
    noncomm_ring
  have hunique :
      dressed = resummedLadderVertex ladder hinvertible bare :=
    eq_resummedLadderVertex_of_fixedPoint
      ladder hinvertible bare dressed hfixed
  have hresummed :
      resummedLadderVertex ladder hinvertible bare =
        scale • resummedLadderVertex ladder hinvertible charge := by
    rw [hbare]
    exact resummedLadderVertex_smul ladder hinvertible scale charge
  rw [hunique, hresummed] at hinsertion
  simpa only [mul_smul_comm, smul_mul_assoc] using hinsertion

end FiniteSCBASolution

/-- Regression for the universal identity-charge specialization of the generic finite Ward bridge.
This is intentionally an anonymous example rather than a second public Ward theorem. -/
example {energy broadening : ℝ}
    {ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)}
    (solution : FiniteSCBASolution ensemble energy broadening)
    (hinvertible :
      IsUnit
        (1 - ensemble.retardedAdvancedLadderCLM
          (solution.green .retarded) (solution.green .advanced))) :
    (spectralParameter .advanced energy broadening -
        spectralParameter .retarded energy broadening) •
      (solution.green .retarded *
        resummedLadderVertex
          (ensemble.retardedAdvancedLadderCLM
            (solution.green .retarded) (solution.green .advanced))
          hinvertible
          (1 : H →L[ℂ] H) *
        solution.green .advanced) =
      solution.green .retarded - solution.green .advanced := by
  simpa using
    solution.resummedLadderVertex_charge_ward_consistency
      (1 : H →L[ℂ] H)
      (ChargeSymmetry.one ensemble)
      hinvertible

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
