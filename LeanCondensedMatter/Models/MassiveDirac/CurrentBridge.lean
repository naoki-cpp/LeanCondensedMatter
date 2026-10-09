import LeanCondensedMatter.QuantumMechanics.SingleParticle.GeneralizedCurrent
import LeanCondensedMatter.Models.MassiveDirac.Model.Operator

set_option linter.style.header false

/-!
# Massive-Dirac generalized-current bridge

The clean massive-Dirac model owns its bounded charge-current vertices independently of the generic
single-particle current construction. This module records the semantic bridge between them without
making the model operator layer depend on localization or weak-current representations.

For either in-plane direction, the bounded current vertex `j_μ = -e v_μ`, viewed as an algebraic
linear map, is exactly the generic symmetrized current for the scalar transported quantity
`(-e) I`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- The massive-Dirac charge-current vertex is the generic one-particle current for transported
quantity `(-e) I`. -/
theorem currentOperator_toLinearMap_eq_symmetrizedVelocityCurrent
    (direction : Fin 2) (e v : ℝ) :
    (currentOperator direction e v).toLinearMap =
      QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent DiracHilbert
        (velocityOperator direction v).toLinearMap
        (((-e : ℝ) : ℂ) • LinearMap.id) := by
  rw [QuantumMechanics.SingleParticle.symmetrizedVelocityCurrent_smul_id]
  rw [currentOperator_eq_charge_smul_velocityOperator]
  rfl

end

end QuantumTheory.Models.MassiveDirac
