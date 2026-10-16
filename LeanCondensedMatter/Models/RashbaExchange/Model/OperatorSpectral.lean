import Mathlib.RingTheory.Idempotents
import LeanCondensedMatter.Models.RashbaExchange.Operator
import LeanCondensedMatter.Models.RashbaExchange.Model.Spectral
import LeanCondensedMatter.Transport.Resolvent.Spectral
import LeanCondensedMatter.Analysis.Operator.FiniteTrace

set_option linter.style.header false

/-!
# Bounded-operator spectral resolvent of the Rashba-exchange model

Gauge-free band projectors are transported to the bounded-operator realization and used to build the
finite two-band projector resolvent.  Away from the band degeneracy, this candidate equals the
canonical resolvent at every nonzero signed imaginary regulator.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open ContinuousLinearMap
open QuantumTheory.Transport

/-- Band projector transported to the bounded-operator representation. -/
noncomputable def bandProjectorOperator
    (params : Parameters) (band : Band) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (bandProjector params band px py)

/-- Ordered current band block `Tr(P_target j_μ P_source j_ν)`. -/
noncomputable def currentBandBlockTrace
    (params : Parameters) (μ ν : Fin 2) (source target : Band) (px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator params target px py *
      currentBoundedOperator params μ px py *
      bandProjectorOperator params source px py *
      currentBoundedOperator params ν px py)

/-- The bounded-operator projectors inherit the complete orthogonal family
from the matrix realization under the algebra equivalence. -/
theorem bandProjectorOperator_completeOrthogonalIdempotents
    (params : Parameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    CompleteOrthogonalIdempotents
      (fun band : Band => bandProjectorOperator params band px py) := by
  let φ : InternalSpace.PauliMatrix ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
    Matrix.toEuclideanCLM
  change CompleteOrthogonalIdempotents
    ((φ.toRingEquiv.toRingHom) ∘
      (fun band : Band => bandProjector params band px py))
  exact (bandProjector_completeOrthogonalIdempotents params px py hE).map
    φ.toRingEquiv.toRingHom

/-- The Hamiltonian acts on each projector with its shifted band energy. -/
theorem hamiltonianOperator_mul_bandProjectorOperator
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    hamiltonianOperator params px py * bandProjectorOperator params band px py =
      (((bandEnergy params band px py : ℝ) : ℂ)) •
        bandProjectorOperator params band px py := by
  unfold hamiltonianOperator bandProjectorOperator matrixOperator
  rw [← map_mul, hamiltonian_mul_bandProjector params band px py hE, map_smul]

/-- Gauge-free finite-band spectral candidate for the resolvent. -/
noncomputable def projectorResolvent
    (z : ℂ) (params : Parameters) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  ∑ band : Band,
    scalarResolventCoefficient z (bandEnergy params band px py) •
      bandProjectorOperator params band px py

end

end QuantumTheory.Models.RashbaExchange
