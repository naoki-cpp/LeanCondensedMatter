import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# Finite localized-spin configuration space

The labels 0,...,2s count spin deviations from the polarized reference at each site.
For finitely many sites the full state space is the canonical finite-dimensional
complex Hilbert space on these configurations. No interaction is assumed.
Source: Stancil-Prabhakar, Section 2.7.1, equation (2.147).
-/

namespace QuantumTheory.LocalizedSpin

/-- Local spin-deviation labels, with the natural parameter representing 2s. -/
abbrev Configuration (twiceSpin : ℕ) (Site : Type*) := Site → Fin (twiceSpin + 1)

/-- Complex amplitudes on localized-spin configurations. The finite-site instance
provides the canonical Hilbert-space structure. -/
abbrev State (twiceSpin : ℕ) (Site : Type*) :=
  EuclideanSpace ℂ (Configuration twiceSpin Site)

end QuantumTheory.LocalizedSpin
