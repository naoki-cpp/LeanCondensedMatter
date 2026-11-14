# Model-independent scattering theory

## Current construction

The bounded Dyson development supplies the operator first variation
K_V(t) = -(i/ℏ) ∫₀ᵗ V_I(s) ds.
The transition-amplitude theorem differentiates its matrix element at zero real coupling.
For orthogonal initial and final vectors, at each fixed finite t,

    lim_(λ→0, λ≠0) |⟨f,U_I,λ(t)i⟩|² / λ² = |⟨f,K_V(t)i⟩|².

This is a statement about exact Dyson amplitudes, not a first-order amplitude substituted into
a probability without error control. Its squared-amplitude interpretation as a probability
requires normalized states and unitary evolution. The existing Hermitian-continuous bounded
perturbation construction supplies unitarity; the algebraic limit itself needs only the stated
bounds and orthogonality.

The model-independent scalar pole convention is rate = 2Γ/ℏ with reciprocal lifetime.
For the damped-pole ansatz, the squared modulus equals exp(-(2Γ/ℏ)t); this does not show that a
general self-adjoint Hamiltonian has exponential survival at all times. Functions remain total,
so inverse zero is zero, not an encoding of infinite lifetime. Physical finite-lifetime use
requires positive Γ and ℏ.

Massive Dirac retains the actual Born self-energy, Fermi projector, metallic/cutoff hypotheses,
and angular overlap calculations. It supplies its damping to the common rate/lifetime laws.
The model-named reciprocal lifetime and generic width-conversion declarations are removed.
Transport lifetime and single-particle lifetime remain distinct quantities.

## Next mathematical and physical steps

1. Specialize the first variation to stationary eigenstates and a static perturbation, deriving
   the finite-time oscillatory transition kernel with all ℏ factors. Reuse the existing
   interaction-picture evolution; do not postulate the scalar amplitude independently.
2. Prove the approximate-identity limit of the positive finite-time kernel against an explicit
   final-energy density or test function. A finite collection of discrete levels alone does not
   yield a universal delta-function transition rate. Keep weak-coupling, long-time, and
   continuum limits distinct; state any order of limits and uniform estimates.
3. Connect the resulting integrated golden-rule rate to the on-shell imaginary part of a
   second-order self-energy under matching spectral-measure and integrability hypotheses.
   Existing Lorentzian finite-window mass results are reusable ingredients, not the complete
   spectral/dynamical bridge. Avoid introducing a Dirac delta as an ordinary real-valued function.
4. Instantiate that shared result with the Massive Dirac density, scalar-impurity covariance,
   physical-momentum normalization, and projector overlap. Remove duplicated generic proof
   routes from the model as each bridge becomes available.
5. Separately relate current relaxation to a collision operator or conserving vertex problem.
   An angularly weighted rate does not by itself prove full Kubo equivalence, and none of the
   preceding steps alone proves a thermodynamic, DC, or zero-broadening conductivity limit.

## Ownership

- Analysis owns oscillatory kernels, approximate identities, measures, and limit arguments.
- QuantumTheory owns transition amplitudes, state interpretation, pole-width conventions, and
  the spectral/dynamical scattering bridge.
- Transport owns current relaxation and conductivity constructions.
- Models own concrete Hamiltonians, spectral data, impurity laws, and normalization choices.

No compatibility forwarders should preserve the old ownership. Each phase migrates its concrete
consumers together with the general theorem that replaces their common argument.