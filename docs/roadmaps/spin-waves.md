# Spin waves roadmap

This roadmap develops localized-spin magnetism through an exact finite-system benchmark,
then separates quantum spin-wave approximations from macroscopic magnetization dynamics.
The design boundary is [ADR 0022](../adr/0022-spin-wave-model-boundaries.md); terminology is
defined in the [magnetism glossary](../glossary/magnetism/CONTEXT.md).

## Source and status

The organizing reference is D. D. Stancil and A. Prabhakar, *Spin Waves: Theory and
Applications* (Springer, 2009), DOI [10.1007/978-0-387-77865-5](https://doi.org/10.1007/978-0-387-77865-5).
Page numbers below refer to printed pages. The book motivates models and derivations;
it does not replace explicit hypotheses or a Lean proof of an approximation estimate.

SW1 and SW2 are `proved`: the finite spin representation and exact one-magnon restriction are
implemented in [SpinHalf/Finite](../../LeanCondensedMatter/QuantumTheory/SpinHalf/Finite.lean)
and [Models/Heisenberg](../../LeanCondensedMatter/Models/Heisenberg.lean). The spectrum and
long-wavelength dispersion are proved in
[SpinWaveSpectrum](../../LeanCondensedMatter/Models/Heisenberg/SpinWaveSpectrum.lean).
SW3 and later targets remain `idea`. General-spin representations, infinite-volume order,
antiferromagnetic Bogoliubov diagonalization, and thin-film boundary modes are later work.

## Existing infrastructure

| Reusable source | Contribution and boundary |
| --- | --- |
| [SpinHalf](../../LeanCondensedMatter/QuantumTheory/SpinHalf.lean) and [Pauli algebra](../../LeanCondensedMatter/Analysis/InternalSpace/Pauli.lean) | Spin-1/2 matrices and Hermitian real spin components; [Finite](../../LeanCondensedMatter/QuantumTheory/SpinHalf/Finite.lean) supplies the full configuration space, site action, exchange identity, and isometric one-magnon embedding. |
| [Bosonic creation/annihilation](../../LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CreationAnnihilation.lean), [CCR](../../LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CCR.lean), and [number operator](../../LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/NumberOperator.lean) | Algebraic occupation-basis actions and commutators; no identification with a finite spin space is supplied. |
| [Completed free Gibbs theory](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/Completed/FreeGibbs.lean) | Finite-mode trace-class Gibbs construction for strictly positive mode energies; a zero-energy mode needs separate treatment. |
| [Bosonic quartic interaction](../../LeanCondensedMatter/SecondQuantization/Bosonic/Diagrammatics/Quartic/Interaction.lean) | Existing ordered four-field vertices; a magnon coefficient and its derivation remain model-specific. |
| [Retarded susceptibility](../../LeanCondensedMatter/QuantumTheory/LinearResponse/RetardedSusceptibility.lean) | Bounded quantum commutator response; microscopic magnetic observables and a comparison with macroscopic susceptibility remain to be constructed. |
| [Crystal lattice](../../LeanCondensedMatter/Crystal/Lattice.lean) and [Brillouin quotient](../../LeanCondensedMatter/Crystal/Brillouin.lean) | Reciprocal-space conventions for later periodic models; the finite-ring Fourier basis uses Mathlib cyclic characters and orthonormal-basis construction. |

The SW1 survey of pinned Mathlib v4.34.1 uses `EuclideanSpace`, coordinate permutations
through `LinearIsometryEquiv.piLpCongrLeft`, `LinearMap.isometryOfInner`, and the existing
symmetric/positive operator APIs. The representation therefore uses canonical finite
function Hilbert spaces rather than introducing a custom inner product or tensor API.
The SW2 survey reuses `ZMod.stdAddChar`, its primitive-character sum, and
`basisOfOrthonormalOfCardEqFinrank` to construct the normalized Fourier basis in
[FiniteCyclic](../../LeanCondensedMatter/Analysis/Fourier/FiniteCyclic.lean).
The small-wavevector limit uses Mathlib's continuous `Real.sinc` and the double-angle
identity. No custom Fourier transform, inner product, or differentiation theory is needed.

## Implementation order and acceptance criteria

### SW1: Exact spin-1/2 ferromagnetic ring (`proved`)

Source: Section 2.5, pp. 46-50, especially (2.71)-(2.92).

Start with a finite periodic ring of N >= 3 sites, uniform J > 0, nearest-neighbor
exchange, and zero external field. Use the full space of complex amplitudes on spin
configurations, with its canonical inner product. A one-spin-flip space is derived as
a subspace, rather than postulated as the original spin system.

Use the book's bond-once convention:

\[
H=-\frac{2J}{\hbar^2}\sum_j \mathbf S_j\cdot\mathbf S_{j+1},\qquad
E_0=-JN/2,\qquad H-E_0I=J\sum_j(I-P_{j,j+1}).
\]

Here P exchanges the two site labels in a spin configuration. Prove the equality of
the spin-product and permutation forms, with nonzero hbar where division is used.
Prove self-adjointness, nonnegativity of the shifted operator, and that the normalized
fully polarized state attains E0. Do not claim uniqueness of the zero-field ground state.

Completion of the first implementation unit requires an isometric embedding U of site
amplitudes into the full spin space and the intertwining identity

\[
(H-E_0I)U=U L_J,\qquad
(L_J\psi)_j=J(2\psi_j-\psi_{j-1}-\psi_{j+1}).
\]

The theorem `Models.Heisenberg.excitationHamiltonian_comp_oneMagnonEmbedding` proves
this intertwining identity for N >= 3. Together with
`hamiltonian_eq_excitation_add_ground` it identifies the shifted full-spin action.
`hamiltonian_eq_spinSum`, `hamiltonian_isSelfAdjoint`, `excitationHamiltonian_isPositive`,
and `hamiltonian_polarized` establish the representation and energy claims. Positivity
is proved under the weaker condition J >= 0; no ground-state uniqueness is claimed.

### SW2: Finite Fourier spectrum and long-wavelength behavior (`proved`)

Dependency: SW1. Source: (2.90)-(2.94), pp. 48-49.

`ZMod.fourierBasis` is a complete normalized Fourier basis;
`oneMagnonLaplacian_fourierBasis` proves its eigenvalue equation for LJ, with

\[
E_q=2J(1-\cos(2\pi q/N)).
\]

`wavevector` gives the representative 2 pi q.val/(N a) for positive lattice spacing a.
`dispersion_wavevector` identifies its energy with the finite-mode eigenvalue.
`excitationHamiltonian_fourierMode` transports the equation to the full spin space
for N >= 3. `oneMagnonEnergy_zero` gives zero shifted energy for q=0;
`oneMagnonEnergy_pos` proves strict positivity for J > 0 and q != 0 modulo N.

For lattice spacing a > 0, define the continuous dispersion expression
E(k)=2J(1-cos(ka)). `tendsto_dispersion_div_sq` proves E(k)/k^2 -> J a^2 through nonzero k.
This limit of an expression does not establish a thermodynamic-limit theorem for states.
Angular frequency is E/hbar with hbar > 0; group velocity and effective mass are optional
consequences after the spectrum is established.

### SW3: Holstein-Primakoff representation and quadratic magnons

Source: Section 2.7.1, pp. 55-60, especially (2.146)-(2.166).

Represent 2s by a natural number and make the physical occupation restriction
0 <= n_j <= 2s explicit. Define the square-root factors on occupation basis states;
preserve the order of those factors and creation/annihilation operators. Prove that
the composite spin operators preserve the physical subspace and realize the spin
algebra, including the endpoint states.

Keep this exact representation separate from the quadratic Hamiltonian obtained by
expanding about the polarized state and retaining terms through degree two. Prove
the quadratic model's finite Fourier diagonalization and preservation of CCR on the
bosonic algebraic domain. Its bond-counting normalization must reproduce SW2 when
specialized consistently. Reconcile the directed-neighbor sum of Section 2.7 with the
bond-once sum of Section 2.5 before transferring numerical coefficients.

An error estimate between exact and quadratic dynamics is a separate target with
specified states, occupation control, time interval, and norm or observable error.
Low mean occupation alone is not a substitute for such a theorem.

### SW4: Free-magnon equilibrium and interactions

Dependency: SW3. Source: Section 2.7.2, pp. 60-63, for the interaction expansion.

First use a strictly positive Zeeman gap, positive inverse temperature, and finitely
many modes to connect the diagonal quadratic model to existing free-boson Gibbs
theory. Derive the magnetization reduction from occupation expectations, with the
magnetic-moment sign and volume normalization stated explicitly.

Treat the zero-field zero mode separately: unrestricted bosonic occupation at zero
energy makes the one-mode partition series divergent, although a finite spin system
has a finite partition function. Any zero-mode constraint or gap-removal limit changes
the hypotheses and must be named. Bloch's low-temperature law and thermodynamic limits
require further dimension-dependent analysis.

For interactions, derive the quartic coefficients in the existing vertex convention
and prove crystal momentum conservation modulo reciprocal lattice vectors. A quartic
formula alone establishes neither stability nor convergence of a Gibbs/Dyson expansion.

### SW5: Macroscopic magnetization and Polder susceptibility

Independent entry point; SW3 is not a prerequisite. Source: Sections 3.7-3.8,
pp. 91-101, especially (3.104), (3.109)-(3.116), and (3.127)-(3.129).

Take the Landau-Lifshitz or Gilbert equation as an explicit macroscopic model. Prove
conservation of magnetization magnitude for differentiable solutions. For a specified
time-independent energy and effective-field convention, prove dissipation with the
correct gyromagnetic and damping signs. Existence of solutions is a separate obligation.

Linearize around a saturated uniform equilibrium and derive the Polder tensor by
solving the transverse system. State the time convention, field units, and nonzero
denominator. Derive the Gilbert modification from the linearized equation rather than
silently assigning a complex frequency. An exact LL/Gilbert conversion must account
for parameter rescaling; equality with unchanged coefficients is not assumed.

Matching this response to microscopic Kubo susceptibility requires a separate model
comparison theorem with matching source coupling, observables, and approximations.

### SW6: Dipolar-exchange waves and finite samples

Dependency: SW5. Source: Sections 5.1-5.2, pp. 139-143.

Under explicit magnetostatic and homogeneous-medium assumptions, derive Walker's
equation and the plane-wave dispersion (5.18), including exchange. State the propagation
angle and stable-equilibrium conditions before selecting a positive square root.

Thin-film surface and volume modes need their own geometry, boundary conditions, and
mode-existence argument. Leave electromagnetic retardation, optical coupling, nonlinear
solitons, spin-torque devices, and material calibration to subsequent model-specific work.

## Delivery and verification

Implement SW1 and SW2 first, with each PR ending in a physical theorem rather than a
collection of unused definitions. SW3-SW4 form the quantum branch; SW5-SW6 form the
macroscopic branch. Exact filenames and additional generalizations follow concrete consumers.

Validate Lean changes through PR CI, without local lake/Lean or Python execution for
this workstream. Review every physical coefficient, approximation, and source convention.
Documentation-only changes require link, scope, and status checks rather than a Lean build.
