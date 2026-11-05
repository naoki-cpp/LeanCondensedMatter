import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.Star

set_option linter.style.header false

/-!
# Antiunitary maps for bounded linear-response systems

An antiunitary is a continuous conjugate-linear equivalence of Hilbert-space
vectors that conjugates the complex inner product. Additivity, semilinearity,
bijectivity, continuity and the inverse map are inherited from Mathlib rather
than repeated as independent structure fields.

Covariance of a particular Hamiltonian or current under this map must be
proved separately for each model.
-/

namespace QuantumTheory.LinearResponse

/-- A continuous conjugate-linear equivalence conjugating the Hilbert-space
inner product. No condition on its square is imposed, so Kramers time reversal
with square minus identity is permitted. -/
structure AntiunitaryMap (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The bijective continuous conjugate-linear action on state vectors. -/
  equiv : H ≃L⋆[ℂ] H
  /-- Antiunitarity: inner products are complex conjugated. -/
  inner_map : ∀ x y,
    inner ℂ (equiv x) (equiv y) = (starRingEnd ℂ) (inner ℂ x y)

end QuantumTheory.LinearResponse
