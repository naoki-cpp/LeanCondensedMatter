import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticThermalConnected

set_option linter.style.header false

/-!
# Imaginary-time-dependent bosonic quartic thermal amplitudes

The coefficientwise connected theorem uses a static thermal amplitude. A Dyson coefficient carries
one imaginary-time variable per interaction vertex. For a free quartic vertex this time dependence
is scalar, because the whole vertex is an eigenoperator of free imaginary-time evolution.

This file isolates that missing analytic seam. It dresses each ordered coefficientwise diagram by
the product of its vertex evolution phases and then integrates that scalar dressing over the ordered
simplex. No identification with the convergence-aware Gibbs expectation of the recursive bosonic
Dyson operator is made here; that interchange of the Gibbs functional with the recursive integral
remains a separate analytic obligation.
-/

namespace SecondQuantization
namespace Bosonic

open Combinatorics

noncomputable section

variable {Mode : Type*} [DecidableEq Mode] {N : ℕ}

/-- Scalar imaginary-time phase of one quartic interaction vertex. -/
noncomputable def quarticVertexThermalPhase (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) : ℂ :=
  Complex.exp ((τ : ℂ) * (Common.quarticVertexEnergyShift ε q : ℂ))

/-- Product of the free-evolution phases of all vertices of an ordered quartic diagram. -/
noncomputable def QuarticDiagram.orderedVertexThermalPhase
    (ε : Mode → ℝ) {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ) : ℂ :=
  ∏ i, quarticVertexThermalPhase ε (d.vertexLabel (order i)) (τ i)

/-- The time-dependent ordered thermal amplitude. All time dependence is carried by the scalar
free-evolution phase; the Wick/contraction value remains the coefficientwise amplitude proved
previously. -/
noncomputable def QuarticDiagram.orderedTimedThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ) : ℂ :=
  d.orderedVertexThermalPhase ε order τ * d.orderedThermalAmplitude ε β g order

/-- Ordered-simplex integral of one ordered bosonic quartic diagram amplitude. -/
noncomputable def QuarticDiagram.orderedSimplexThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) : ℂ :=
  intervalIntegral.orderedSimplexIntegral S.card β
    (d.orderedTimedThermalAmplitude ε β g order)

omit [DecidableEq Mode] in
/-- The vertex phase is continuous in imaginary time. -/
theorem continuous_quarticVertexThermalPhase (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) :
    Continuous (quarticVertexThermalPhase ε q) := by
  unfold quarticVertexThermalPhase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

omit [DecidableEq Mode] in
/-- The full ordered vertex-phase product is jointly continuous in all vertex times. -/
theorem QuarticDiagram.continuous_orderedVertexThermalPhase
    (ε : Mode → ℝ) {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    Continuous (d.orderedVertexThermalPhase ε order) := by
  classical
  unfold QuarticDiagram.orderedVertexThermalPhase
  exact continuous_finsetProd _ fun i _ =>
    (continuous_quarticVertexThermalPhase ε (d.vertexLabel (order i))).comp (continuous_apply i)

/-- The timed ordered amplitude is jointly continuous in the vertex times. -/
theorem QuarticDiagram.continuous_orderedTimedThermalAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    Continuous (d.orderedTimedThermalAmplitude ε β g order) := by
  unfold QuarticDiagram.orderedTimedThermalAmplitude
  exact (d.continuous_orderedVertexThermalPhase ε order).mul continuous_const

/-- The static coefficientwise amplitude factors out of the ordered-simplex integral. -/
theorem QuarticDiagram.orderedSimplexThermalAmplitude_eq_phaseIntegral_mul
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    d.orderedSimplexThermalAmplitude ε β g order =
      intervalIntegral.orderedSimplexIntegral S.card β
        (d.orderedVertexThermalPhase ε order) *
          d.orderedThermalAmplitude ε β g order := by
  rw [QuarticDiagram.orderedSimplexThermalAmplitude]
  unfold QuarticDiagram.orderedTimedThermalAmplitude
  have h := intervalIntegral.orderedSimplexIntegral_smul S.card β
    (d.orderedThermalAmplitude ε β g order)
    (d.orderedVertexThermalPhase ε order)
  simpa [mul_comm] using h

/-- The time-dependent amplitude has an honest ordered-simplex integral, supplied directly by its
joint continuity. -/
theorem QuarticDiagram.continuous_orderedSimplexThermalAmplitude_in_bound
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {S : Finset (Fin N)} (d : QuarticDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    Continuous (fun t : ℝ => intervalIntegral.orderedSimplexIntegral S.card t
      (d.orderedTimedThermalAmplitude ε β g order)) := by
  exact intervalIntegral.continuous_orderedSimplexIntegral_of_continuous S.card id
    (fun _ τ => d.orderedTimedThermalAmplitude ε β g order τ) continuous_id
    ((d.continuous_orderedTimedThermalAmplitude ε β g order).comp continuous_snd)

end
end Bosonic
end SecondQuantization
