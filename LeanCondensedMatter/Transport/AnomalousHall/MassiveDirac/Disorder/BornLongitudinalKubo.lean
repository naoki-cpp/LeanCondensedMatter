import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornPropagatorOperator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced

set_option linter.style.header false

/-!
# Born-dressed longitudinal retarded-advanced Kubo channel

This module inserts the massive-Dirac Born propagator into the generic finite-dimensional
retarded-advanced vertex trace block.  The measured vertex is the physical `x` charge current, while
the source vertex is supplied explicitly so a finite-broadening dressed current can be inserted
without first replacing it by its weak-disorder scalar limit.

No exact disorder average, weak-disorder limit, clean DC limit, SCBA/Ward statement, or RTA
conductivity theorem is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Pointwise finite-Born-width longitudinal RA trace channel with the physical `x` current as the
measured vertex and an arbitrary supplied source/dressed vertex. -/
noncomputable def continuumBornLongitudinalRetardedAdvancedTraceKernel
    (e v m px py probeEnergy disorderStrength hbar : ℝ)
    (dressedVertex : DiracHilbert →L[ℂ] DiracHilbert) : ℂ :=
  retardedAdvancedVertexTraceKernel
    (currentOperator .x e v)
    (continuumBornGreenOperator
      .retarded v m px py probeEnergy disorderStrength hbar)
    dressedVertex
    (continuumBornGreenOperator
      .advanced v m px py probeEnergy disorderStrength hbar)

/-- When the supplied dressed vertex is given by a concrete `2 × 2` matrix, the Born RA channel is
exactly the ordinary matrix trace of the corresponding four-factor block. -/
theorem continuumBornLongitudinalRetardedAdvancedTraceKernel_matrixVertex
    (e v m px py probeEnergy disorderStrength hbar : ℝ) (vertex : Matrix2) :
    continuumBornLongitudinalRetardedAdvancedTraceKernel
        e v m px py probeEnergy disorderStrength hbar (matrixOperator vertex) =
      Matrix.trace
        (current .x e v *
          continuumBornGreenMatrix
            .retarded v m px py probeEnergy disorderStrength hbar *
          vertex *
          continuumBornGreenMatrix
            .advanced v m px py probeEnergy disorderStrength hbar) := by
  unfold continuumBornLongitudinalRetardedAdvancedTraceKernel
    retardedAdvancedVertexTraceKernel twoGreenVertexTraceKernel
    continuumBornGreenOperator currentOperator
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change finiteDimensionalOperatorTrace
      (φ (current .x e v) *
        φ (continuumBornGreenMatrix
          .retarded v m px py probeEnergy disorderStrength hbar) *
        φ vertex *
        φ (continuumBornGreenMatrix
          .advanced v m px py probeEnergy disorderStrength hbar)) = _
  rw [← map_mul, ← map_mul, ← map_mul]
  exact finiteDimensionalOperatorTrace_matrixOperator _

end

end AnomalousHall.MassiveDirac
