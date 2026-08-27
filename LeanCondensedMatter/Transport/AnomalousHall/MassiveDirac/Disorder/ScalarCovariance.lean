import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Response
import LeanCondensedMatter.Transport.Disorder.RetardedBorn
import LeanCondensedMatter.Transport.Disorder.AdvancedBorn

set_option linter.style.header false

/-!
# Finite scalar disorder for the massive-Dirac AHE model

This module starts Phase 4 of #1269 by connecting the concrete two-level massive-Dirac Hilbert
space to the repository's canonical exact finite-disorder second moment and Born self-energies.

The scalar assumption in this first slice is only an internal-space statement:

```text
Vω = uω I
```

on `DiracHilbert`. Under that exact finite-ensemble hypothesis,

```text
E[Vω X Vω] = E[uω²] X.
```

The theorem is exact for the supplied finite ensemble. It does not yet encode continuum momentum
transfer, white-noise delta covariance, a thermodynamic limit, or a weak-disorder closure. In
particular, the Born self-energies below remain Born objects; they are not identified with exact
disorder-averaged Green operators.
-/

namespace AnomalousHall.MassiveDirac

open scoped BigOperators

noncomputable section

open QuantumTheory QuantumTheory.Transport

variable {Ω : Type*} [Fintype Ω]
variable {v m px py : ℝ}

/-- Exact finite scalar-disorder specialization of the massive-Dirac model at one momentum.

`impurityPotential_eq` says that disorder is scalar only in the two-component Dirac internal
space. Spatial/momentum correlations are intentionally not represented by this first finite slice. -/
structure FiniteScalarDisorderModel (Ω : Type*) [Fintype Ω]
    (v m px py : ℝ) where
  /-- Canonical exact finite disorder ensemble. -/
  ensemble : FiniteDisorderEnsemble (H := DiracHilbert) (Ω := Ω)
  /-- Real scalar impurity amplitude in each finite configuration. -/
  amplitude : Ω → ℝ
  /-- The clean part of the ensemble is the massive-Dirac Hamiltonian at the supplied momentum. -/
  baseHamiltonian_eq :
    ensemble.baseHamiltonian.1 = hamiltonianOperator v m px py
  /-- Every impurity potential is proportional to the identity in Dirac internal space. -/
  impurityPotential_eq : ∀ ω,
    (ensemble.impurityPotential ω).1 =
      (amplitude ω : ℂ) • (1 : DiracHilbert →L[ℂ] DiracHilbert)

namespace FiniteScalarDisorderModel

variable (model : FiniteScalarDisorderModel Ω v m px py)

/-- Weighted finite scalar second moment `E[uω²]`, represented in `ℂ` so it acts directly on
bounded complex-linear operators. -/
noncomputable def secondMomentStrength : ℂ :=
  ∑ ω, (model.ensemble.probability ω : ℂ) * (model.amplitude ω : ℂ) ^ 2

/-- The canonical exact finite second-moment action becomes scalar multiplication when every
impurity potential is scalar in the Dirac internal space. -/
theorem exactSecondMoment_eq_strength_smul
    (kernel : DiracHilbert →L[ℂ] DiracHilbert) :
    model.ensemble.exactSecondMoment kernel =
      model.secondMomentStrength • kernel := by
  rw [model.ensemble.exactSecondMoment_eq_operatorAverage]
  unfold FiniteDisorderEnsemble.operatorAverage secondMomentStrength
  change
    (∑ ω, (model.ensemble.probability ω : ℂ) •
      ((model.ensemble.impurityPotential ω).1 * kernel *
        (model.ensemble.impurityPotential ω).1)) =
      (∑ ω, (model.ensemble.probability ω : ℂ) * (model.amplitude ω : ℂ) ^ 2) • kernel
  calc
    (∑ ω, (model.ensemble.probability ω : ℂ) •
      ((model.ensemble.impurityPotential ω).1 * kernel *
        (model.ensemble.impurityPotential ω).1)) =
        ∑ ω, ((model.ensemble.probability ω : ℂ) * (model.amplitude ω : ℂ) ^ 2) • kernel := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [model.impurityPotential_eq ω]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, pow_two]
    _ = (∑ ω, (model.ensemble.probability ω : ℂ) * (model.amplitude ω : ℂ) ^ 2) • kernel := by
      rw [← Finset.sum_smul]

/-- The clean retarded Green operator of this finite ensemble is the retarded resolvent of the
concrete massive-Dirac Hamiltonian. -/
theorem freeRetardedGreen_eq_massiveDirac
    (energy broadening : ℝ) :
    model.ensemble.freeRetardedGreen energy broadening =
      retardedResolvent (hamiltonianOperator v m px py) energy broadening := by
  unfold FiniteDisorderEnsemble.freeRetardedGreen
  rw [model.baseHamiltonian_eq]

/-- The clean advanced Green operator of this finite ensemble is the advanced resolvent of the
concrete massive-Dirac Hamiltonian. -/
theorem freeAdvancedGreen_eq_massiveDirac
    (energy broadening : ℝ) :
    model.ensemble.freeAdvancedGreen energy broadening =
      advancedResolvent (hamiltonianOperator v m px py) energy broadening := by
  unfold FiniteDisorderEnsemble.freeAdvancedGreen
  rw [model.baseHamiltonian_eq]

/-- Massive-Dirac scalar-disorder retarded Born self-energy. This is the exact finite second moment
applied to the clean retarded propagator, not an exact disorder-averaged self-energy. -/
theorem bornRetardedSelfEnergy_eq_strength_smul
    (energy broadening : ℝ) :
    model.ensemble.bornRetardedSelfEnergy energy broadening =
      model.secondMomentStrength •
        retardedResolvent (hamiltonianOperator v m px py) energy broadening := by
  rw [model.ensemble.bornRetardedSelfEnergy_eq_secondMoment]
  rw [model.exactSecondMoment_eq_strength_smul]
  rw [model.freeRetardedGreen_eq_massiveDirac]

/-- Massive-Dirac scalar-disorder advanced Born self-energy. As on the retarded side, no equality
with the exact disorder average is claimed. -/
theorem bornAdvancedSelfEnergy_eq_strength_smul
    (energy broadening : ℝ) :
    model.ensemble.bornAdvancedSelfEnergy energy broadening =
      model.secondMomentStrength •
        advancedResolvent (hamiltonianOperator v m px py) energy broadening := by
  rw [model.ensemble.bornAdvancedSelfEnergy_eq_secondMoment]
  rw [model.exactSecondMoment_eq_strength_smul]
  rw [model.freeAdvancedGreen_eq_massiveDirac]

end FiniteScalarDisorderModel

end

end AnomalousHall.MassiveDirac
