import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Disorder.Born

set_option linter.style.header false

/-!
# Finite scalar disorder for the massive-Dirac AHE model

This module starts Phase 4 of #1269 by connecting the concrete two-level massive-Dirac Hilbert
space to the repository's canonical exact finite-disorder second moment and Born self-energy.

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
particular, the Born self-energy below remains a Born object; it is not identified with an exact
disorder-averaged Green operator.
-/

namespace AnomalousHall.MassiveDirac

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
  model.ensemble.scalarSecondMomentStrength model.amplitude

/-- The canonical exact finite second-moment action becomes scalar multiplication when every
impurity potential is scalar in the Dirac internal space. -/
theorem exactSecondMoment_eq_strength_smul
    (kernel : DiracHilbert →L[ℂ] DiracHilbert) :
    model.ensemble.exactSecondMoment kernel =
      model.secondMomentStrength • kernel := by
  exact model.ensemble.exactSecondMoment_eq_scalarSecondMomentStrength_smul
    model.amplitude model.impurityPotential_eq kernel

/-- Massive-Dirac scalar-disorder first-Born self-energy at an arbitrary signed regulator. This is
the exact finite second moment applied to the corresponding clean propagator, not an exact
disorder-averaged self-energy. -/
theorem bornSelfEnergyOfRegulator_eq_strength_smul
    (energy regulator : ℝ) :
    model.ensemble.bornSelfEnergyOfRegulator energy regulator =
      model.secondMomentStrength •
        resolvent (hamiltonianOperator v m px py)
          (spectralParameterOfRegulator energy regulator) := by
  unfold FiniteDisorderEnsemble.bornSelfEnergyOfRegulator
  rw [model.exactSecondMoment_eq_strength_smul]
  unfold FiniteDisorderEnsemble.freeGreenOfRegulator
  rw [model.baseHamiltonian_eq]

end FiniteScalarDisorderModel

end

end AnomalousHall.MassiveDirac
