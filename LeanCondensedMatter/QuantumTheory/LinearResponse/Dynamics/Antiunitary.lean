import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.header false

/-!
# Antiunitary maps for bounded linear-response systems

A concrete antiunitary is supplied with its conjugate-linearity, inner-product
conjugation, and bijectivity properties. This structure is independent of
Hamiltonians, time evolution, conductivity, and the choice of physical currents.

The covariance of a Hamiltonian or current under this map must be proved
separately for each model; neither is an axiom of an arbitrary antiunitary.
-/

namespace QuantumTheory.LinearResponse

/-- A bijective conjugate-linear Hilbert-space map preserving the inner product
up to complex conjugation. This records the antiunitary laws without introducing
a second complex-linear operator representation. -/
structure AntiunitaryMap (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- Map on state vectors. -/
  toFun : H → H
  /-- Additivity of the map. -/
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Conjugate-linearity of the map. -/
  map_smul : ∀ (c : ℂ) (x : H),
    toFun (c • x) = ((starRingEnd ℂ) c) • toFun x
  /-- Inner products are complex-conjugated under the map. -/
  inner_map : ∀ x y,
    inner ℂ (toFun x) (toFun y) = (starRingEnd ℂ) (inner ℂ x y)
  /-- Surjectivity and injectivity, completing the antiunitary equivalence. -/
  bijective : Function.Bijective toFun

end QuantumTheory.LinearResponse
