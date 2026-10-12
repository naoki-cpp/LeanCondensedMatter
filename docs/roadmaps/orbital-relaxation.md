# Orbital and spin relaxation in centrosymmetric models

This roadmap concerns the Dyakonov-Perel-like relaxation mechanism studied by
Sohn, Lee, and Lee (2024). The paper and its supplemental material motivate the
target; Lean statements must be defined from explicit models and hypotheses,
not copied from an approximate calculation. No declaration in this repository
currently proves the relaxation law below.

Tracking issue: [#3360](https://github.com/naoki-cpp/LeanCondensedMatter/issues/3360).

## Target and boundary

The first target is the orbital sector of a centrosymmetric, three-dimensional
spin-1 `p`-orbital model. At a fixed momentum magnitude `k`, let `Lᵢ` be the
dimensionless spin-1 orbital matrices and set

```text
Hₒₘ(k) = c₁ ∑ᵢ kᵢ² Lᵢ² + c₂ ∑_{i ≠ j} kᵢ kⱼ {Lᵢ, Lⱼ}.
```

The sum convention for the off-diagonal term must be fixed before proving a
coefficient: an ordered `i ≠ j` sum counts each pair twice. With real `c₁,c₂`,
this Hamiltonian is Hermitian and even in momentum. The scalar `c₀|k|² I`
does not affect the commutator dynamics. These finite-matrix statements are
exact targets.

For a nonnegative rotationally invariant elastic-scattering kernel `W`, define

```text
Iₗ = (1/2) ∫_{-1}^{1} W(u) (1 - Pₗ(u)) du,
τₘ = 1/I₁,       τ₂ = 1/I₂,       γ = τₘ/τ₂ = I₂/I₁.
```

Integrability and `I₁,I₂ > 0` are explicit hypotheses. The degree-two
angular component of `Hₒₘ` is the relevant collision mode. The first physical
endpoint is the conditional orbital rate

```text
Γₒ(k) = (2 k⁴ / (15 ℏ²)) (2 c₁² + 3 c₂²) τ₂
      = (2 k⁴ / (15 ℏ² γ)) (2 c₁² + 3 c₂²) τₘ,
```

with `ℏ > 0`, fixed `|k|`, and the stated perturbative closure. A theorem
should identify the exact matrix and angular-average calculation that produces
the coefficient. Positivity of the rate and the inverse dependence of the
relaxation time on `τₘ` then follow under nonzero coupling.

The perturbative density-matrix ansatz and second-order kinetic equation in
the supplement are approximations. An initial formalization may take the
effective double-commutator equation as a named physical hypothesis. A later,
stronger result could derive it from a specified Boltzmann equation with a
remainder estimate or a controlled weak-coupling limit. Neither route may
silently turn `≈` into equality. The linearized matrix ansatz is not
automatically positive for arbitrary polarization, so positivity is either a
separate bounded-polarization hypothesis or outside the linearized statement.

## Work sequence

1. **Finite orbital benchmark.** Define the spin-1 matrices and `Hₒₘ`, fix
   units and the off-diagonal sum convention, and prove Hermiticity, inversion
   symmetry, trace identities, and the relevant double-commutator identity.
2. **Angular and collision benchmark.** Prove the needed moments of the
   normalized sphere measure, including fourth-order moments. Specify an
   isotropic elastic collision operator and show its action on the degree-two
   polynomial subspace is multiplication by `-I₂`; distinguish this from the
   momentum relaxation mode `I₁`.
3. **Orbital relaxation endpoint.** Under a stated second-order closure,
   derive the averaged orbital equation, its rate `Γₒ(k)`, and exponential
   decay. Keep a fixed-radius result separate from any Fermi-surface or
   finite-temperature average.
4. **Spin extension.** Add spin-1/2 on the tensor product, spin-orbit coupling,
   and a specified orbital band or projector. Treat the degenerate orbital
   subspace explicitly before deriving a spin rate. Strong spin-orbit coupling
   and total-angular-momentum relaxation form a later, distinct benchmark.

The paper's Pt tight-binding simulations, fitted device relaxation lengths,
interface effects, anisotropy, and the conversion from length to time require
additional material, boundary, and diffusion assumptions. They are evidence
for the mechanism, not consequences of the finite kinetic benchmark.

## Existing repository boundary

`QuantumTheory.DensityOperator` and finite-dimensional expectations provide
state-level foundations. `QuantumTheory.SpinHalf.spinMatrix` provides the
physical spin-1/2 normalization, while `Analysis.InternalSpace.Pauli` provides
dimensionless representation matrices. The existing
`Transport.Analysis.AngularHarmonics` API concerns a two-dimensional polar
angle; it does not supply the three-dimensional sphere moments needed here.
The finite disorder and transport response APIs describe different observables
and should only be connected by a separate identification theorem.

## Source checks before stating the endpoint

- The supplement defines `1/τₘ = I₁` and `1/τ* = I₂`, but prints
  `γ = τₘ/τ* = I₁/I₂` in Eq. (18), repeated in Eqs. (36) and (55). Algebra
  gives `γ = I₂/I₁`. Its rate formula uses `τ* = τₘ/γ` and is consistent with
  the verbal definition of `γ`. Use the definitions above and record any
  comparison with the printed ratio as a source discrepancy.
- Confirm the coefficient and orbital-coupling notation across the main text
  and supplement before stating the spin endpoint; their displayed
  Hamiltonians use different coefficient labels.
- The replacement of a momentum average by `k = k_F` is an additional
  low-energy approximation. It is not part of the fixed-radius theorem.

## Source

Jeonghun Sohn, Jongjun M. Lee, and Hyun-Woo Lee, “Dyakonov-Perel-like Orbital
and Spin Relaxations in Centrosymmetric Systems,” *Physical Review Letters*
**132**, 246301 (2024), [DOI: 10.1103/PhysRevLett.132.246301](https://doi.org/10.1103/PhysRevLett.132.246301),
and its supplemental material, Sec. I.

