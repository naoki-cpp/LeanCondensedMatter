import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite parabolic two-dimensional electron gas

This module owns the clean Hamiltonian and velocity of an isotropic parabolic two-dimensional
electron gas,

```text
ε(p) = |p|² / (2 m_eff).
```

The band, Hamiltonian and velocity depend only on `HamiltonianParameters`, carrying the
effective mass. The finite-response parameter bundle and cutoff domain live in
`ResponseParameters`; model-specific Green functions live in `Green`, and charge-current
vertices and conductivity calculations live in `Response`. No infinite-volume,
cutoff-removal, or zero-broadening limit is assumed in this clean model.
-/

namespace QuantumTheory.Models.Parabolic2DEG

noncomputable section

/-- Effective mass determining the clean parabolic band, Hamiltonian and group velocity. -/
structure HamiltonianParameters where
  /-- Effective mass `m_eff` in the parabolic dispersion. -/
  effectiveMass : ℝ

/-- The one-band Hilbert space used by the scalar parabolic benchmark. -/
abbrev BandHilbert := ℂ

/-- Cartesian momentum component selected by a coordinate in `Fin 2`. -/
def momentumComponent (direction : Fin 2) (px py : ℝ) : ℝ :=
  if direction = 0 then px else py

/-- Parabolic band energy `ε(p) = |p|² / (2 m_eff)`. -/
def bandEnergy (params : HamiltonianParameters) (px py : ℝ) : ℝ :=
  (px ^ 2 + py ^ 2) / (2 * params.effectiveMass)

/-- Cartesian group-velocity component `v_i = p_i / m_eff`. -/
def velocityComponent
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) : ℝ :=
  momentumComponent direction px py / params.effectiveMass

/-- One-band Hamiltonian operator, represented as scalar multiplication on `ℂ`. -/
noncomputable def hamiltonianOperator
    (params : HamiltonianParameters) (px py : ℝ) : BandHilbert →L[ℂ] BandHilbert :=
  (((bandEnergy params px py : ℝ) : ℂ)) •
    (1 : BandHilbert →L[ℂ] BandHilbert)

/-- One-band velocity operator represented by the named velocity component. -/
noncomputable def velocityOperator
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) :
    BandHilbert →L[ℂ] BandHilbert :=
  (((velocityComponent params direction px py : ℝ) : ℂ)) •
    (1 : BandHilbert →L[ℂ] BandHilbert)

/-- The Hamiltonian operator is self-adjoint because its scalar coefficient is real. -/
theorem hamiltonianOperator_isSelfAdjoint
    (params : HamiltonianParameters) (px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator params px py) := by
  simp [hamiltonianOperator, isSelfAdjoint_iff]

/-- The velocity operator is self-adjoint because its scalar coefficient is real. -/
theorem velocityOperator_isSelfAdjoint
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) :
    IsSelfAdjoint (velocityOperator params direction px py) := by
  simp [velocityOperator, isSelfAdjoint_iff]

end

end QuantumTheory.Models.Parabolic2DEG
