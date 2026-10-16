import Mathlib.RingTheory.Idempotents
import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Models.MassiveDirac.Model.Spectral
import LeanCondensedMatter.Transport.Resolvent.Spectral

set_option linter.style.header false

/-!
# Bounded-operator spectral resolvent of the massive-Dirac model

The massive-Dirac model has explicit gauge-independent rank-one band projectors `P₋` and `P₊`.
This module transports those projectors to the bounded-operator realization and connects them to the
generic transport resolvent, without choosing eigenvectors or introducing a response formalism.

Away from the band degeneracy,

```text
G(z) = ∑ₙ (z - Eₙ)⁻¹ Pₙ
```

is the finite spectral expansion. This module owns the model projectors and their Hamiltonian
action; general finite-sum and resolvent identities live upstream in Analysis and Transport.
Kubo–Bastin, Středa, propagator, and disorder consumers remain downstream.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open ContinuousLinearMap

/-- A massive-Dirac band projector transported to the bounded-operator representation used by the
transport stack. -/
noncomputable def bandProjectorOperator (band : Band) (v m px py : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (bandProjector band v m px py)

/-- Every band projector is a nonzero bounded operator. -/
theorem bandProjectorOperator_ne_zero (band : Band) (v m px py : ℝ) :
    bandProjectorOperator band v m px py ≠ 0 := by
  intro hzero
  have hmatrix : bandProjector band v m px py = 0 := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [bandProjectorOperator, matrixOperator] using hzero
  have htrace := congrArg Matrix.trace hmatrix
  simpa using htrace

/-- Ordered current band block `Tr(P_target j_μ P_source j_ν)` in the bounded-operator model. -/
noncomputable def currentBandBlockTrace
    (μ ν : Fin 2) (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator target v m px py * currentOperator μ e v *
      bandProjectorOperator source v m px py * currentOperator ν e v)

/-- The bounded-operator projectors inherit the complete orthogonal family
from the matrix realization under the algebra equivalence. -/
theorem bandProjectorOperator_completeOrthogonalIdempotents
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    CompleteOrthogonalIdempotents
      (fun band : Band => bandProjectorOperator band v m px py) := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) :=
    Matrix.toEuclideanCLM
  change CompleteOrthogonalIdempotents
    ((φ.toRingEquiv.toRingHom) ∘
      (fun band : Band => bandProjector band v m px py))
  exact (bandProjector_completeOrthogonalIdempotents v m px py hE).map
    φ.toRingEquiv.toRingHom

/-- The Hamiltonian acts on each operator projector with its band energy. -/
theorem hamiltonianOperator_mul_bandProjectorOperator
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonianOperator v m px py * bandProjectorOperator band v m px py =
      (((bandEnergy band v m px py : ℝ) : ℂ)) •
        bandProjectorOperator band v m px py := by
  unfold hamiltonianOperator bandProjectorOperator matrixOperator
  rw [← map_mul, hamiltonian_mul_bandProjector band v m px py hE, map_smul]

/-- Gauge-free finite-band spectral candidate for the resolvent of the massive-Dirac Hamiltonian. -/
noncomputable def projectorResolvent
    (z : ℂ) (v m px py : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∑ band : Band,
    scalarResolventCoefficient z (bandEnergy band v m px py) •
      bandProjectorOperator band v m px py

end

end QuantumTheory.Models.MassiveDirac
