import LeanCondensedMatter.Transport.Disorder.TwoParticle
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import Mathlib.Analysis.Normed.Operator.Mul

set_option linter.style.header false

/-!
# Exact finite-disorder two-Green Středa trace bridge

The two-Green trace kernel is averaged configuration by configuration before any product of
disorder averages is formed. Its exact finite-ensemble decomposition follows from the canonical
connected two-particle insertion and the ordinary finite-dimensional operator trace.

This does not identify the connected term with a noncrossing vertex correction, nor does it
supply the RR/AA remainder, sea term, contact term, conductivity normalization, or any limit.
-/

namespace QuantumTheory
namespace Transport

open scoped BigOperators

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [FiniteDimensional ℂ H] [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Average of the canonical two-Green trace kernel equals the trace of the canonical exact
two-operator insertion. This is valid for arbitrary operator families and a fixed source vertex. -/
theorem average_twoGreenVertexTraceKernel_eq_trace_insertion
    (measuredVertex sourceVertex : H →L[ℂ] H)
    (left right : Ω → H →L[ℂ] H) :
    ensemble.average (fun ω =>
        twoGreenVertexTraceKernel measuredVertex (left ω) sourceVertex (right ω)) =
      ContinuousLinearMap.finiteDimensionalOperatorTrace
        (measuredVertex * ensemble.averagedOperatorInsertion left right sourceVertex) := by
  calc
    ensemble.average (fun ω =>
        twoGreenVertexTraceKernel measuredVertex (left ω) sourceVertex (right ω)) =
      ContinuousLinearMap.finiteDimensionalOperatorTrace
        (ensemble.average (fun ω =>
          measuredVertex * (left ω * sourceVertex * right ω))) := by
        calc
          _ = ensemble.average (fun ω =>
              ContinuousLinearMap.finiteDimensionalOperatorTrace
                (measuredVertex * (left ω * sourceVertex * right ω))) := by
            apply congrArg ensemble.average
            funext ω
            simp only [twoGreenVertexTraceKernel, mul_assoc]
          _ = _ := (ensemble.map_average
            (ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H)).toLinearMap
            (fun ω => measuredVertex * (left ω * sourceVertex * right ω))).symm
    _ = ContinuousLinearMap.finiteDimensionalOperatorTrace
        (measuredVertex * ensemble.averagedOperatorInsertion left right sourceVertex) := by
      apply congrArg ContinuousLinearMap.finiteDimensionalOperatorTrace
      simpa [averagedOperatorInsertion] using (ensemble.map_average
        ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H) measuredVertex 1).toLinearMap)
        (fun ω => left ω * sourceVertex * right ω)).symm

/-- Exact ensemble average of the supplied two-Green Středa trace block. It is not a
conductivity and does not discard same-side or sea response terms. -/
noncomputable def averagedTwoGreenVertexTraceKernelOfRegulators
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (measuredVertex sourceVertex : H →L[ℂ] H) : ℂ :=
  ensemble.average (fun ω =>
    twoGreenVertexTraceKernel measuredVertex
      (ensemble.configurationGreenOfRegulator energyLeft regulatorLeft ω)
      sourceVertex
      (ensemble.configurationGreenOfRegulator energyRight regulatorRight ω))

/-- Exact decomposition of the averaged two-Green trace into the trace of mean Green operators
and the trace of the connected disorder insertion, with noncommutative operator order intact.
The retarded/advanced channel is obtained by supplying the corresponding signed regulators. -/
theorem averagedTwoGreenVertexTraceKernelOfRegulators_eq_mean_add_connected
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (measuredVertex sourceVertex : H →L[ℂ] H) :
    ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight measuredVertex sourceVertex =
      twoGreenVertexTraceKernel measuredVertex
        (ensemble.averagedGreenOfRegulator energyLeft regulatorLeft)
        sourceVertex
        (ensemble.averagedGreenOfRegulator energyRight regulatorRight) +
      ContinuousLinearMap.finiteDimensionalOperatorTrace
        (measuredVertex * ensemble.connectedTwoGreenInsertionOfRegulators
          energyLeft regulatorLeft energyRight regulatorRight sourceVertex) := by
  calc
    ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight measuredVertex sourceVertex =
      ContinuousLinearMap.finiteDimensionalOperatorTrace
        (measuredVertex * ensemble.averagedTwoGreenInsertionOfRegulators
          energyLeft regulatorLeft energyRight regulatorRight sourceVertex) := by
        simpa only [averagedTwoGreenVertexTraceKernelOfRegulators,
          averagedTwoGreenInsertionOfRegulators] using
          (ensemble.average_twoGreenVertexTraceKernel_eq_trace_insertion
            measuredVertex sourceVertex
            (fun ω => ensemble.configurationGreenOfRegulator energyLeft regulatorLeft ω)
            (fun ω => ensemble.configurationGreenOfRegulator energyRight regulatorRight ω))
    _ = _ := by
      rw [ensemble.averagedTwoGreenInsertionOfRegulators_eq_mean_add_connected]
      simp only [mul_add, map_add, twoGreenVertexTraceKernel, mul_assoc]

/-- Exact deviation of an averaged two-Green trace from a supplied dressed-vertex RA trace.
The three terms inside the trace respectively measure the left and right one-particle Green
mismatches and the connected vertex remainder. No equality between an exact disorder average
and a noncrossing or SCBA approximation is assumed. -/
theorem averagedTwoGreenVertexTraceKernelOfRegulators_sub_dressed_eq
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (measuredVertex bareSourceVertex : H →L[ℂ] H)
    (suppliedLeftGreen dressedSourceVertex suppliedRightGreen : H →L[ℂ] H) :
    ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        energyLeft regulatorLeft energyRight regulatorRight
        measuredVertex bareSourceVertex -
      retardedAdvancedVertexTraceKernel
        measuredVertex suppliedLeftGreen dressedSourceVertex suppliedRightGreen =
      ContinuousLinearMap.finiteDimensionalOperatorTrace
        (measuredVertex *
          ((ensemble.averagedGreenOfRegulator energyLeft regulatorLeft -
              suppliedLeftGreen) * bareSourceVertex *
              ensemble.averagedGreenOfRegulator energyRight regulatorRight +
            suppliedLeftGreen * bareSourceVertex *
              (ensemble.averagedGreenOfRegulator energyRight regulatorRight -
                suppliedRightGreen) +
            ensemble.connectedTwoGreenInsertionOfRegulators
              energyLeft regulatorLeft energyRight regulatorRight bareSourceVertex -
            suppliedLeftGreen * (dressedSourceVertex - bareSourceVertex) *
              suppliedRightGreen)) := by
  let meanLeft := ensemble.averagedGreenOfRegulator energyLeft regulatorLeft
  let meanRight := ensemble.averagedGreenOfRegulator energyRight regulatorRight
  let connected := ensemble.connectedTwoGreenInsertionOfRegulators
    energyLeft regulatorLeft energyRight regulatorRight bareSourceVertex
  let trace := ContinuousLinearMap.finiteDimensionalOperatorTrace (H := H)
  have hoperator :
      measuredVertex * meanLeft * bareSourceVertex * meanRight +
          measuredVertex * connected -
          measuredVertex * suppliedLeftGreen * dressedSourceVertex * suppliedRightGreen =
        measuredVertex *
          ((meanLeft - suppliedLeftGreen) * bareSourceVertex * meanRight +
            suppliedLeftGreen * bareSourceVertex * (meanRight - suppliedRightGreen) +
            connected -
            suppliedLeftGreen * (dressedSourceVertex - bareSourceVertex) *
              suppliedRightGreen) := by
    noncomm_ring
  rw [ensemble.averagedTwoGreenVertexTraceKernelOfRegulators_eq_mean_add_connected]
  change
    trace (measuredVertex * meanLeft * bareSourceVertex * meanRight) +
        trace (measuredVertex * connected) -
        trace (measuredVertex * suppliedLeftGreen * dressedSourceVertex *
          suppliedRightGreen) =
      trace (measuredVertex *
        ((meanLeft - suppliedLeftGreen) * bareSourceVertex * meanRight +
          suppliedLeftGreen * bareSourceVertex * (meanRight - suppliedRightGreen) +
          connected -
          suppliedLeftGreen * (dressedSourceVertex - bareSourceVertex) *
            suppliedRightGreen))
  simpa only [map_add, map_sub] using congrArg trace hoperator

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
