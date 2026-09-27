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

/-- With velocity fixed, the generalized one-particle current is complex-linear in the transported
one-body quantity. -/
noncomputable def symmetrizedVelocityCurrentLinear
    (velocity : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  _root_.ConservationLaw.symmetrizedProductLeftLinear V velocity

/-- The generalized one-particle current operator `jᵐ = 1/2 {v,m}`. -/
noncomputable def symmetrizedVelocityCurrent
    (velocity m : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  symmetrizedVelocityCurrentLinear V velocity m

@[simp]
theorem symmetrizedVelocityCurrentLinear_apply
    (velocity m : V →ₗ[ℂ] V) :
    symmetrizedVelocityCurrentLinear V velocity m =
      symmetrizedVelocityCurrent V velocity m :=
  rfl

/-- A scalar transported quantity `q I` gives the charge-like current `q v`. -/
@[simp]
theorem symmetrizedVelocityCurrent_smul_id
    (velocity : V →ₗ[ℂ] V) (q : ℂ) :
    symmetrizedVelocityCurrent V velocity (q • LinearMap.id) = q • velocity := by
  change _root_.ConservationLaw.symmetrizedProduct velocity (q • LinearMap.id) = q • velocity
  exact _root_.ConservationLaw.symmetrizedProduct_smul_id velocity q

@[simp]
theorem symmetrizedVelocityCurrent_id
    (velocity : V →ₗ[ℂ] V) :
    symmetrizedVelocityCurrent V velocity LinearMap.id = velocity := by
  simpa using symmetrizedVelocityCurrent_smul_id V velocity (1 : ℂ)

end SingleParticle
end QuantumMechanics
