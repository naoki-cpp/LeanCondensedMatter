import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass
import LeanCondensedMatter.Analysis.TraceClassScalar
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.Exp

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Canonical (Gibbs) density operator via trace-class operators (infinite dimensions)

Extends the canonical (Gibbs) density operator `e^{-βH}/Z(β)` (`QuantumTheory.gibbsState` in
`QuantumTheory/Entropy.lean`) beyond finite-dimensional `H`, via Mathlib's continuous functional
calculus `cfc` (which, unlike this project's own eigenbasis-sum construction in the
finite-dimensional file, needs no finite-dimensionality: `Analysis/CFC.lean`'s own docstring notes
`cfc` is the natural infinite-dimensional replacement for such sums).

**This file is additive, not a replacement**: the finite-dimensional `QuantumTheory.gibbsState`
and everything built on it are untouched.

**Scope note — explicit hypotheses, not derived assumptions.** A physical Hamiltonian's spectrum
need not be discrete, so `e^{-βH}` need not be compact or trace-class in general (matching the
Hilbert space setting used throughout this project). Rather than formalizing a sufficient
discreteness-of-spectrum condition on `Hop` itself, `gibbsState` below takes compactness and
trace-class-ness of the (unnormalized) Gibbs operator `e^{-βH}`, and non-vanishing of its
trace `Z(β)`, as *explicit hypotheses* — matching this project's established style for
`QuantumTheory.TraceClass.DensityOperator`/`POVM` (see
`notes/roadmaps/quantum-theory-foundations.md`) of taking such spectral facts as inputs rather
than deriving them from more primitive physical
assumptions.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The (unnormalized) Gibbs operator `e^{-βH}`**, via the continuous functional calculus. -/
noncomputable def gibbsOp (Hop : Observable H) (β : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => Real.exp (-β * x)) Hop.1

/-- `gibbsOp` is positive, since `x ↦ e^{-βx}` is everywhere nonnegative: the continuous
functional calculus of a nonnegative function is nonnegative in the C⋆-algebra order
(`cfc_nonneg`), which coincides with `ContinuousLinearMap.IsPositive` on `H →L[ℂ] H`
(`nonneg_iff_isPositive`). -/
theorem gibbsOp_isPositive (Hop : Observable H) (β : ℝ) : (gibbsOp Hop β).IsPositive := by
  rw [gibbsOp, ← nonneg_iff_isPositive]
  exact cfc_nonneg (fun x _ => (Real.exp_pos _).le)

/-- **Canonical (Gibbs) density operator (infinite-dimensional).** The normalized Gibbs state
`e^{-βH}/Z(β)`, given a Hamiltonian `Hop`, inverse temperature `β`, and explicit hypotheses that
the (unnormalized) Gibbs operator `e^{-βH}` is compact and trace-class with nonzero trace `Z(β)`
(see the module docstring for why these are taken as hypotheses rather than derived). -/
noncomputable def gibbsState (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (htc : ContinuousLinearMap.IsTraceClass (gibbsOp Hop β))
    (hZ : ContinuousLinearMap.trace htc ≠ 0) : DensityOperator H where
  op := (ContinuousLinearMap.trace htc)⁻¹ • gibbsOp Hop β
  pos := by
    rw [ContinuousLinearMap.real_smul_eq_complex_smul]
    refine (gibbsOp_isPositive Hop β).smul_of_nonneg ?_
    have hZnonneg : 0 ≤ ContinuousLinearMap.trace htc :=
      ContinuousLinearMap.trace_nonneg htc (gibbsOp_isPositive Hop β).toLinearMap
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hZnonneg)
  compact := hcompact.smul _
  traceClass := ContinuousLinearMap.isTraceClass_smul (inv_ne_zero hZ) htc
  trace_eq_one := by
    rw [ContinuousLinearMap.trace_smul (inv_ne_zero hZ) htc
      (ContinuousLinearMap.isTraceClass_smul (inv_ne_zero hZ) htc)]
    exact inv_mul_cancel₀ hZ

end QuantumTheory.TraceClass
