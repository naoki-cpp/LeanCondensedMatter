import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct

set_option linter.style.header false

/-!
# Generalized one-particle current operators

For a distinguished one-particle velocity `v` and transported one-body quantity `m`, this module
owns the operator-level generalized-current candidate

```text
jᵐ = 1/2 {v,m}.
```

The construction is independent of localization, continuity equations, weak differentials, and
response theory. Those semantics are supplied downstream by `SymmetrizedVelocityCurrent` and the
conservation-law representation layer.

With `v` fixed, the current is complex-linear in the transported quantity. Scalar quantities
`q I` reduce to the charge-like form `q v`.
-/

namespace QuantumMechanics
namespace SingleParticle

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The generalized one-particle current operator `jᵐ = 1/2 {v,m}`. -/
noncomputable def symmetrizedVelocityCurrent
    (velocity m : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  _root_.LinearMap.symmetrizedProduct (K := ℂ) velocity m

end SingleParticle
end QuantumMechanics
