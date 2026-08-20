# Second-quantization terminology

Preferred physical terminology and the corresponding Lean concepts. Use the physical term in prose
and mention an identifier only when the implementation matters.

| Term | Meaning in this project | Primary implementation |
|---|---|---|
| Algebraic Fock space | Finite-support linear combinations of occupation configurations. It is not a completed Hilbert space. | `SecondQuantization/Common/Algebra/AlgebraicFock.lean` |
| Finite Hilbert Fock realization | `EuclideanSpace ℂ Config` for finite `Config`, used to interpret algebraic operators as bounded finite-dimensional operators. | `SecondQuantization/Common/Thermal/FiniteHilbertOperator.lean` |
| Mode index type | A type of one-particle labels. It does not by itself carry a one-particle Hilbert-space structure. | `SecondQuantization/Common/Algebra/OneParticleSpace.lean` |
| Occupation configuration | Fermionic or bosonic occupation data. The zero configuration is not yet the vacuum vector until embedded in Fock space. | `SecondQuantization/Fermionic/Algebra/Occupation.lean`, `SecondQuantization/Bosonic/Algebra/Occupation.lean` |
| Basis state | The algebraic Fock vector associated with one occupation configuration. | `basisState` |
| Matrix coefficient | Coordinate evaluation of an algebraic operator between basis states. Do not call it a Hilbert-space matrix element until a Hilbert realization is specified. | `matrixCoeff` |
| Exchange commutator | `[A,B]ζ = A ∘ B - ζ B ∘ A`. It is a reordering identity, not a contraction. | `SecondQuantization/Common/Algebra/ExchangeCommutator.lean` |
| Imaginary-time ordering | Ordering operator factors by imaginary time, with the statistics sign inserted on exchange. It is not thermal until evaluated in a thermal state. | `SecondQuantization/Common/ImaginaryTime/TimeOrdering.lean` |
| Diagonal imaginary-time evolution | Basis-diagonal algebraic evolution by exponential energy factors. It is not automatically an operator exponential on completed Fock space. | `SecondQuantization/Common/ImaginaryTime/DiagonalEvolution.lean` |
| Boltzmann weight | `exp (-β E(i))`. The pure-point definition accepts real `β`; physical applications state any required sign assumption separately. | `QuantumTheory.purePointBoltzmannWeight`, free fermionic/bosonic thermal modules |
| Partition function | The normalized-state denominator obtained by summing positive Boltzmann weights or taking the spectral trace of a Gibbs operator. Reserve the term for the Gibbs specialization, not an arbitrary weight sum. | `QuantumTheory.purePointPartitionFunction`, `QuantumTheory.gibbsOp` |
| Pure-point Gibbs state | Density operator constructed directly from a Hilbert basis, real energy levels, and Boltzmann summability; the finite specialization requires no separate state implementation. | `QuantumTheory/Gibbs/PurePoint.lean` |
| Density-state expectation | The canonical normalized expectation of a bounded operator in a density state. | `QuantumTheory.DensityOperator.expectation` |
| Finite Gibbs expectation | Density-state expectation of the generic finite pure-point Gibbs state after transporting an algebraic Fock operator to the finite Hilbert realization. | `SecondQuantization.Common.finiteGibbsExpectation` |
| Weighted trace | An unnormalized finite coordinate sum with an arbitrary weight. It is proof infrastructure, not a physical state by itself. | `SecondQuantization/Common/Thermal/FiniteWeightedTrace.lean` |
| Normalized weighted diagonal | A normalized coordinate functional for an arbitrary finite complex weight. Call it Gibbs only after the Boltzmann specialization and density-state comparison. | `SecondQuantization/Common/Thermal/WeightedDiagonalFunctional.lean` |
| Thermal contraction | The c-number expectation of an imaginary-time-ordered operator pair in a specified thermal state. It is not the operator identity used to exchange two factors. | finite Gibbs two-point and contraction modules |
| Perfect pairing | A complete matching of a finite set of operator positions. It is combinatorial and contains no expectation value. | `Combinatorics/PerfectPairing.lean` |
| Pair deletion and reindexing | The induction operation that removes one matched pair and transports the remaining pairing to a smaller index type. It is not a physical process. | `eraseZeroPair` |
| Crossing number | The number of interleaving paired arcs `a < c < b < d`. | `SecondQuantization/Common/Thermal/BlochDeDominicis/PairingWeight.lean` |
| Statistics weight | `ζ ^ crossingCount`, with `ζ = +1` for bosons and `ζ = -1` for fermions. | `Pairing.weight` |
| Bloch–de Dominicis theorem | Pairing expansion of thermal moments in a free or quasifree Gaussian Gibbs state. It is not a theorem for arbitrary interacting Gibbs states. | `SecondQuantization/Common/Thermal/BlochDeDominicis/` |
| Generic expectation pairing recursion | State-independent contract containing normalized expectation, pair values, admissibility, and the first-pair KMS/exchange recurrence. | `ExpectationPairingRecursion` |
| Linked-cluster theorem | Statement that coefficients of the logarithm of the normalized partition function are connected contributions. Formal and analytic versions have separate hypotheses. | fermionic linked-cluster modules and Track B cumulant modules |
| Pure-state density embedding | `ψ ↦ |ψ⟩⟨ψ|`. This is not purification of a mixed state on a larger Hilbert space. | `QuantumTheory.pure` |
| Von Neumann entropy | `ENNReal`-valued density-state entropy. It may be infinite outside finite-dimensional or summability-controlled settings. | `QuantumTheory.vonNeumannEntropy` |
| Boltzmann’s principle | Physical identification of `k_B` times von Neumann entropy with thermodynamic entropy. The equality is not formalized. | `notes/model-and-assumptions.md` |

## Naming rules

- Reserve “state” and “expectation” for normalized positive functionals or density operators with the
  required proofs.
- Reserve “Gibbs” and “thermal” for positive Boltzmann specializations, not arbitrary complex
  weights.
- Keep operator reordering, time ordering, pairings, and contractions distinct.
- Distinguish algebraic coordinate identities from completed Hilbert-space operator statements.
- State free/quasifree assumptions whenever invoking a pairings-only thermal expansion.
