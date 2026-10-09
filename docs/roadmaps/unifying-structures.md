# Unifying mathematical structures: candidate roadmap

Status: `idea`. The existing abstraction principle is recorded in
[ADR 0021](../adr/0021-intrinsic-mathematical-structures.md); this roadmap lists prospective
applications of that principle, not further accepted decisions.

This is a design inventory, not an implemented API or a commitment to add
a typeclass for every item. The aim is to discover mathematical structures that turn several
physics-specific statements into specializations of one canonical theorem, in the same spirit as
using the exchange scalar `ζ`, linear maps, and basis-independent operators.

A candidate is worth implementing only when it has an independent mathematical meaning and a
concrete consumer that becomes simpler. Prefer existing Mathlib structures and current project
owners; do not create forwarding wrappers or competing representations. Recheck the pinned
Mathlib API before starting implementation.

## Candidates and current boundaries

| Candidate | Existing canonical infrastructure | Possible new generalization | Priority |
| --- | --- | --- | --- |
| Z₂-graded operator algebra | `Statistics.zetaInt`, `ExchangeAlgebra`, `ScalarExchange.zetaCommutator` | Homogeneous parity and a graded commutator for mixed even/odd operators | First experiment |
| Multisource generating functional | Finite-set normalized moments/cumulants, formal-log bridge, connected decompositions | Genuine multi-insertion source variables and connected correlation functions | High, consumer-driven |
| Parameter-dependent Green operators | `IsSelfEnergy`, resolvents, `SpectralSide`, SCBA | Analytic operator-valued Green families with a shared domain | Conditional |
| Shuffle algebra of iterated integrals | `FamilySlotShuffleTo`, ordered-simplex integrands | Product-to-shuffle identities at a justified scalar-integral boundary | High, after audit |
| Source-dependent Hamiltonian | Linear-response source coupling, observable variation/contact term | Derive generalized force/current and contact response from source derivatives | High |
| Projector-based non-Abelian Berry geometry | Pointwise eigenbasis data, `PeriodicBlochProjector` | Curvature and parallel transport of occupied subspaces without a global frame | Research |
| Contour-ordered correlation functions | Imaginary-time ordering and thermal pairing | A shared contour/order representation with real- and imaginary-time consumers | Later |
| Projective symmetry representations | Crystal symmetry and operator representation layers | Cocycle-controlled projective representations, e.g. magnetic translations | Later |

## 1. Z₂-graded operator algebra

For homogeneous operators with degrees `|A|, |B| ∈ Z₂`, define the graded bracket

```text
[A, B]_gr = A B - (-1)^(|A||B|) B A.
```

Even-even and even-odd pairs give an ordinary commutator; odd-odd pairs give an
anticommutator. A graded multiplication law relates the degree of a product to the sum
of degrees. This extends, rather than replaces, the existing single-statistics
`ζ ∈ {+1, -1}` exchange interface.

Current anchors: [exchange algebra](../../LeanCondensedMatter/SecondQuantization/Common/Algebra/ExchangeAlgebra.lean),
[statistics](../../LeanCondensedMatter/SecondQuantization/Common/Algebra/Statistics.lean),
[generic exchange signs](../../LeanCondensedMatter/Combinatorics/ExchangeSign.lean), and
[pairing weights](../../LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/PairingWeight.lean).

Implementation gate: survey Mathlib's graded algebra API, specify homogeneous components
rather than assigning every algebra element a unique degree, then derive at least one
existing exchange identity and one genuinely mixed even/odd identity. Preserve the
current bosonic/fermionic Fock representation and analytic-domain boundaries. A new
class is unjustified if it merely renames `ζ` for one species.

## 2. Multisource generating functional

The present finite-set and formal-power-series theory already proves
moment–cumulant inversion and formal-log/connected-contribution bridges.
A possible next step is a *genuine* source functional, schematically

```text
Z[J] = expectation (T exp(source-coupled operator)),
W[J] = log Z[J].
```

Distinct source coefficients or derivatives should produce ordered higher-point
correlators; their connected counterparts should come from `W`. Unlike the
existing zero-source formal partition series, the new object must carry physical
external-insertion semantics.

Current anchors: [finite connected decompositions](../../LeanCondensedMatter/Combinatorics/Cumulant/ConnectedDecomposition.lean),
[formal-log/cumulant bridge](../../LeanCondensedMatter/Analysis/PowerSeries/Cumulant.lean),
and [linked-cluster roadmap](linked-cluster-theorem.md).

Implementation gate: first exhibit pre-normalized external-insertion moments and a
higher-point consumer that cannot use the normalized finite-set API directly.
Identify the exact algebra of sources: commuting variables work for bosonic sources
but fermionic field sources require an appropriate anticommuting/Grassmann
formalism. Do not assert analytic differentiation or convergence from a purely
formal generating series.

## 3. Parameter-dependent operator-valued Green functions

The fixed-parameter, noncommutative Dyson relation is **already** abstract:
`IsSelfEnergy G₀ G Σ` records both orientations of `G = G₀ + G₀ Σ G`, and
inverse-difference results have explicit inverse hypotheses. A parallel
`DysonEquation` class would add no value.

The potential missing abstraction is a common operator-valued family `G(z)`,
with its resolvent domain, analyticity, adjoint reflection, and a possibly
energy-dependent `Σ(z)`. It would organize retarded/advanced boundary
specializations without suppressing spectral-domain or regulator assumptions.

Current anchors: [Dyson self-energy](../../LeanCondensedMatter/Transport/Resolvent/SelfEnergy.lean),
[resolvent and spectral sides](../../LeanCondensedMatter/Transport/Resolvent/Basic.lean),
and [finite SCBA solution](../../LeanCondensedMatter/Transport/Disorder/SCBA.lean).

Implementation gate: identify two consumers needing the same parameter-domain
theorems; prove at least one shared analytic or adjoint statement. Keep exact
disorder averages separate from Born/SCBA approximations, and do not infer
real-axis boundary values without a limiting argument.

## 4. Shuffle algebra of time-ordered integrals

The scalar iterated-integral identity

```text
I(u) I(v) = ∑ (w in shuffles(u, v)) I(w)
```

suggests treating time-order decompositions as a product law, rather than
reproving each ordering split. The repository already owns slot shuffles,
ambient time-coordinate selection, and regularity of shuffled integrands.

Current anchor: [family shuffle integrands](../../LeanCondensedMatter/Analysis/OrderedSimplex/FamilyShuffleIntegrand.lean).

Implementation gate: audit existing shuffle/ordered-simplex theorems before
introducing an algebra object. Show a concrete product identity for scalar,
integrable, commutative-valued integrands and replace at least two downstream
reindexing proofs. Noncommutative operator products need a separately justified
ordered-product formulation; the scalar shuffle identity must not be applied
to them by analogy.

## 5. Source-dependent Hamiltonian and response derivatives

A differentiable source family `H(λ)` can define a generalized force/current
`J(λ) = -∂H(λ)/∂λ` and its contact response `∂J/∂λ`.
This can put paramagnetic and explicit-observable-variation terms under a
single derivative-based origin, without hard-coding a particular coordinate
representation or assuming every current is uniquely determined by a source.

Current anchor: [observable variation and contact terms](../../LeanCondensedMatter/QuantumTheory/LinearResponse/ObservableVariation.lean).

Implementation gate: prove a reusable result that specializes to both a
source-derived current and its first contact term, and connect it to an existing
response consumer. Supply differentiability, operator-domain, source-coupling
and sign conventions explicitly. Gauge invariance, continuity equations, and
`proper` spin currents require separate hypotheses; they must not follow
from a generic derivative definition by assertion.

## 6. Projector-based non-Abelian Berry geometry

The repository already represents smooth periodic orthogonal projectors,
and finite-band Berry geometry is available through pointwise eigenbasis
data. The next layer could use a subspace projector `P(k)` and its
derivatives to define non-Abelian curvature, schematically

```text
F_μν = P [∂_μ P, ∂_ν P] P,
```

up to the chosen connection and sign convention. Such a construction does
not require a globally smooth eigenvector frame.

Current anchors: [periodic Bloch projectors](../../LeanCondensedMatter/Transport/Topology.lean)
and [pointwise Berry curvature](../../LeanCondensedMatter/Analysis/Operator/BerryGeometry/Curvature.lean).

Implementation gate: first bridge an existing projector consumer to a
frame-independent curvature theorem, fixing signs and identifying whether
the target is a scalar trace curvature or an endomorphism-valued curvature.
Keep global regularity, spectral gaps, Brillouin-zone integration, and
Chern-integrality hypotheses distinct. Do not introduce a second projector
type in place of Mathlib's `IsStarProjection`.

## 7. Contour-ordered correlation functions

A contour and its ordering relation might organize imaginary-time,
real-time retarded, and Keldysh correlation functions through shared
ordering/restriction operations.

Current anchor: [imaginary-time ordering](../../LeanCondensedMatter/SecondQuantization/Common/ImaginaryTime/TimeOrdering.lean).

Implementation gate: exhibit a theorem used by both an existing imaginary-time
consumer and an actual real-time/contour consumer before adding a contour
hierarchy. Specify contour orientation, equal-time ordering, statistics signs,
KMS boundary conditions, and operator domains; an abstract order alone does
not supply these physical facts.

## 8. Projective representations of symmetries

A projective action satisfies `U(g) U(h) = ω(g,h) U(gh)`, where `ω` obeys a
2-cocycle identity. This can model symmetry actions in which physical
states are unchanged by a phase, notably magnetic translations and
projective actions of rotation groups.

Implementation gate: identify a concrete symmetry/model theorem that needs a
nontrivial cocycle; first reuse Mathlib's available group-cohomology and
representation infrastructure where applicable. A spin-half representation
is linear for `SU(2)` but projective for `SO(3)`; record the actual group
rather than conflating the two. This is a new research direction, not a
refactoring target for existing diagrammatics.

## Selection and review criteria

Prioritize a small experiment in the Z₂-graded exchange layer. Multisource
generating functions and source-derived response are the most promising
physics-facing follow-ups; shuffle products merit an upstream combinatorics
audit before any new public API.

For each proposed abstraction:

1. Find the relevant Mathlib API and identify the existing canonical owner.
2. Write the proposed generic theorem and at least two concrete consumers.
3. Check whether it removes duplicated definitions/proofs rather than adding
   a forwarding layer; prefer a theorem or explicit `structure` to a
   `class` unless instance inference is genuinely canonical.
4. Keep sign, statistics, normalization, domain, convergence, and regularity
   assumptions visible at their actual boundaries.
5. Implement and compile a focused pilot before committing to a broader
   migration; update this roadmap with the resulting current design.

No definitions, theorems, or physics guarantees are introduced by this
document.
