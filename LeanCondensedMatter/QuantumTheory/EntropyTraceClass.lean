import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Von Neumann entropy via trace-class operators (infinite dimensions)

Extends the von Neumann entropy (`QuantumTheory.vonNeumannEntropy` in
`QuantumTheory/Entropy.lean`) beyond finite-dimensional `H`, computed from the eigenvalues of a
`QuantumTheory.TraceClass.DensityOperator` (`ContinuousLinearMap.EigenvectorIndex`) rather than a
finite `Fin n`-indexed eigenvalue list.

**This file is additive, not a replacement**: the finite-dimensional `QuantumTheory.Entropy` and
everything built on it are untouched.

**Scope note (a genuine mathematical fact, not a Lean technicality):** in finite dimensions
`vonNeumannEntropy` is a finite sum, so it is automatically real-valued and finite. In infinite
dimensions the analogous sum `-Σᵢ λᵢ ln λᵢ` ranges over a countably infinite family: even though
`Σᵢ λᵢ` converges (`ρ` is trace-class), the entropy sum `Σᵢ (-λᵢ ln λᵢ)` — despite every term
being nonnegative — can genuinely diverge (e.g. `λᵢ = c / (i log² i)` for suitable `c`, summable,
but `-λᵢ ln λᵢ ~ c / (i log i)`, not summable). This is a real physical phenomenon (a trace-class
density operator can have infinite von Neumann entropy), not an artifact of the formalization, so
`vonNeumannEntropy` below is `ENNReal`-valued (`[0, ∞]`) rather than `ℝ`-valued: the sum is always
well-defined, with divergence showing up honestly as `⊤` rather than being silently truncated to
the junk value `0` that a real-valued `tsum` would give.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The eigenvalues of a density operator are nonnegative** — they are the probabilities `p_i`
of measuring the system in the corresponding eigenstate, matching the finite-dimensional
`QuantumTheory.eigenvalues_nonneg`. -/
theorem eigenvalue_nonneg (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) : 0 ≤ a.1.1 :=
  eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a

/-- **The von Neumann entropy `-Tr[ρ ln ρ]` of a density operator (infinite-dimensional)**,
computed from `ρ`'s eigenvalues via `ContinuousLinearMap.EigenvectorIndex`. `ENNReal`-valued
(`[0, ∞]`), unlike the finite-dimensional `QuantumTheory.vonNeumannEntropy`: see the module
docstring above for why the entropy sum can genuinely diverge even for a trace-class `ρ`. -/
noncomputable def vonNeumannEntropy (ρ : DensityOperator H) : ENNReal :=
  ∑' a : EigenvectorIndex ρ.op, ENNReal.ofReal (Real.negMulLog a.1.1)

end QuantumTheory.TraceClass
