import LeanCondensedMatter.Analysis.CompactSelfAdjoint
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Axiomatic quantum theory: density operators via trace-class operators (infinite dimensions)

Extends the density-operator postulate (`QuantumTheory.DensityOperator` in
`QuantumTheory/DensityOperator.lean`) beyond finite-dimensional `H`, using the general
`ContinuousLinearMap.trace` for compact self-adjoint trace-class operators
(`LeanCondensedMatter/Analysis/CompactSelfAdjoint.lean`) in place of `LinearMap.trace`, which
requires finite-dimensionality.

**This file is additive, not a replacement**: the finite-dimensional `QuantumTheory.DensityOperator`
and everything built on it (`POVM`, `prob`, `sum_prob_eq_one`, `purity`, ...) are untouched. This
namespace develops the infinite-dimensional analogue in parallel.

**Scope note (a genuine mathematical gap, not just a Lean technicality):** in finite dimensions
`LinearMap.trace` is defined unconditionally, so `Tr[E_m ρ]` (the Born-rule probability, needed
for `prob`/`sum_prob_eq_one`) makes sense for *any* positive `E_m` and density operator `ρ`. In
this infinite-dimensional setting, `ContinuousLinearMap.trace` is only meaningful for *compact
self-adjoint trace-class* operators — and `E_m ∘ ρ` need not be self-adjoint at all (a product of
two self-adjoint operators is self-adjoint only when they commute). Porting `prob`/`sum_prob_eq_one`
therefore needs a notion of trace for non-self-adjoint (e.g. Hilbert–Schmidt-class) operators that
does not yet exist in this project; see `notes/roadmaps/operator-algebra.md`. This file is
deliberately scoped to what's well-posed without that: the `DensityOperator` structure itself and
properties of a single density operator (`pure`, and eventually `purity`, which only needs `ρ ∘ ρ`
— self-adjoint since `ρ` is).
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Density operator postulate (infinite-dimensional).** A positive, compact, trace-class
operator of trace `1`. The compactness and trace-class hypotheses are carried explicitly (rather
than derived from positivity/boundedness alone, which is not in general enough) — matching the
style of `ContinuousLinearMap.trace_add`/`trace_comp_comm`, which also take these as explicit
hypotheses. -/
structure DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying operator. -/
  op : H →L[ℂ] H
  /-- A density operator is positive. -/
  pos : op.IsPositive
  /-- A density operator is a compact operator, needed for `ContinuousLinearMap.trace` (via its
  eigenbasis) to correctly capture `op`'s action. -/
  compact : IsCompactOperator op
  /-- A density operator is trace-class: its eigenvalues (with multiplicity) are absolutely
  summable. -/
  traceClass : op.IsTraceClass
  /-- A density operator has trace `1`. -/
  trace_eq_one : trace traceClass = 1

/-- A density operator's underlying operator is self-adjoint (in the `IsSymmetric` sense used
throughout `Analysis/CompactSelfAdjoint.lean`), inherited from positivity. -/
theorem DensityOperator.isSymmetric (ρ : DensityOperator H) : (ρ.op : H →ₗ[ℂ] H).IsSymmetric :=
  ρ.pos.isSelfAdjoint.isSymmetric

/-- **A rank-one operator `|x⟩⟨y|` is a compact operator**, regardless of the (possibly
infinite) dimension of `H`: it factors as the composition of the (automatically compact, since
its codomain `ℂ` is locally compact) functional `y ↦ ⟪y, ·⟫` with the continuous linear map
`c ↦ c • x`, and `IsCompactOperator` is preserved under post-composition by a continuous linear
map. -/
theorem isCompactOperator_rankOne (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y : H →L[ℂ] H) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)

end QuantumTheory.TraceClass
