#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MARKER = "## Bosonic specializations already exposed"

# Canonical physical source paths after the Common, Fermionic, Bosonic, and
# statistics-specific Bloch–de Dominicis layout refactors.
PATH_REPLACEMENTS: dict[str, str] = {
    # Fermionic algebra.
    "Fermionic/Occupation.lean": "Fermionic/Algebra/Occupation.lean",
    "Fermionic/FockSpace.lean": "Fermionic/Algebra/FockSpace.lean",
    "Fermionic/CreationAnnihilation.lean": "Fermionic/Algebra/CreationAnnihilation.lean",
    "Fermionic/ParticleNumberCharge.lean": "Fermionic/Algebra/ParticleNumberCharge.lean",
    "Fermionic/CanonicalAnticommutationRelations.lean": "Fermionic/Algebra/CanonicalAnticommutationRelations.lean",
    "Fermionic/ExchangeAlgebra.lean": "Fermionic/Algebra/ExchangeAlgebra.lean",
    "Fermionic/NumberOperator.lean": "Fermionic/Algebra/NumberOperator.lean",
    "Fermionic/Hamiltonian.lean": "Fermionic/Algebra/Hamiltonian.lean",
    "Fermionic/WeightedNumberOperator.lean": "Fermionic/Algebra/WeightedNumberOperator.lean",
    # Fermionic imaginary time.
    "Fermionic/ImaginaryTimeEvolution.lean": "Fermionic/ImaginaryTime/ImaginaryTimeEvolution.lean",
    "Fermionic/InteractionPicture.lean": "Fermionic/ImaginaryTime/InteractionPicture.lean",
    # Fermionic thermal.
    "Fermionic/WeightedFreeTwoPointFunction.lean": "Fermionic/Thermal/WeightedFreeTwoPointFunction.lean",
    "Fermionic/FreeBoltzmannWeight.lean": "Fermionic/Thermal/FreeBoltzmannWeight.lean",
    "Fermionic/FreePartitionFunction.lean": "Fermionic/Thermal/FreePartitionFunction.lean",
    "Fermionic/FreeTwoPointFunction.lean": "Fermionic/Thermal/FreeTwoPointFunction.lean",
    "Fermionic/WeightedContraction.lean": "Fermionic/Thermal/WeightedContraction.lean",
    "Fermionic/QuantumLinkedCluster.lean": "Fermionic/Thermal/QuantumLinkedCluster.lean",
    "Fermionic/BlochDeDominicis/": "Fermionic/Thermal/BlochDeDominicis/",
    # Fermionic perturbation.
    "Fermionic/FormalLogPartitionFunction.lean": "Fermionic/Perturbation/FormalLogPartitionFunction.lean",
    "Fermionic/DysonExpansion.lean": "Fermionic/Perturbation/DysonExpansion.lean",
    "Fermionic/DysonExpansionVerification.lean": "Fermionic/Perturbation/DysonExpansionVerification.lean",
    "Fermionic/DysonPartitionSeries.lean": "Fermionic/Perturbation/DysonPartitionSeries.lean",
    "Fermionic/DysonVertexMoment.lean": "Fermionic/Perturbation/DysonVertexMoment.lean",
    # Fermionic diagrammatics.
    "Fermionic/QuarticInteraction.lean": "Fermionic/Diagrammatics/QuarticInteraction.lean",
    "Fermionic/QuarticLocalLeg.lean": "Fermionic/Diagrammatics/QuarticLocalLeg.lean",
    "Fermionic/DysonDiagramExpansion.lean": "Fermionic/Diagrammatics/DysonDiagramExpansion.lean",
    "Fermionic/WickDiagramConnected.lean": "Fermionic/Diagrammatics/WickDiagram/Connected.lean",
    "Fermionic/WickDiagram/": "Fermionic/Diagrammatics/WickDiagram/",
    "Fermionic/WickDiagram.lean": "Fermionic/Diagrammatics/WickDiagram.lean",
    # Bosonic algebra and imaginary time.
    "Bosonic/Occupation.lean": "Bosonic/Foundations/Occupation.lean",
    "Bosonic/FockSpace.lean": "Bosonic/Foundations/FockSpace.lean",
    "Bosonic/CreationAnnihilation.lean": "Bosonic/OperatorAlgebra/CreationAnnihilation.lean",
    "Bosonic/CCR.lean": "Bosonic/OperatorAlgebra/CCR.lean",
    "Bosonic/NumberOperator.lean": "Bosonic/OperatorAlgebra/NumberOperator.lean",
    "Bosonic/ExchangeAlgebra.lean": "Bosonic/OperatorAlgebra/ExchangeAlgebra.lean",
    "Bosonic/ImaginaryTimeEvolution.lean": "Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean",
    # The former wrapper was folded into the current imaginary-time implementation.
    "Bosonic/ImaginaryTimeOrdering.lean": "Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean",
    # Bosonic thermal.
    "Bosonic/FreePartitionFunction.lean": "Bosonic/Thermal/FreePartitionFunction.lean",
    "Bosonic/BoltzmannWeightFactorization.lean": "Bosonic/Thermal/BoltzmannWeightFactorization.lean",
    "Bosonic/BoltzmannWeightSummable.lean": "Bosonic/Thermal/BoltzmannWeightSummable.lean",
    "Bosonic/ParticleNumberWeightSummable.lean": "Bosonic/Thermal/ParticleNumberWeightSummable.lean",
    "Bosonic/FreeTwoPointCoefficient.lean": "Bosonic/Thermal/FreeTwoPointCoefficient.lean",
    "Bosonic/BlochDeDominicis/": "Bosonic/Thermal/BlochDeDominicis/",
    # Bosonic diagrammatics.
    "Bosonic/QuarticInteraction.lean": "Bosonic/Diagrammatics/QuarticInteraction.lean",
    "Bosonic/QuarticLocalLeg.lean": "Bosonic/Diagrammatics/QuarticLocalLeg.lean",
    "Bosonic/QuarticDiagram.lean": "Bosonic/Diagrammatics/QuarticDiagram.lean",
    "Bosonic/QuarticDiagramWeight.lean": "Bosonic/Diagrammatics/QuarticDiagramWeight.lean",
    "Bosonic/QuarticLegFamily.lean": "Bosonic/Diagrammatics/QuarticLegFamily.lean",
    # Common Bloch–de Dominicis physical file paths.
    "Common/BlochDeDominicis/": "Common/Thermal/BlochDeDominicis/",
    "SecondQuantization/Common/BlochDeDominicisPairing.lean": "Combinatorics/PerfectPairing.lean",
}


def replace_paths(text: str) -> str:
    for old, new in sorted(PATH_REPLACEMENTS.items(), key=lambda item: len(item[0]), reverse=True):
        text = text.replace(old, new)
    return text


def write_if_changed(path: Path, text: str) -> None:
    old = path.read_text(encoding="utf-8")
    if old != text:
        path.write_text(text, encoding="utf-8")


def update_audit() -> None:
    path = ROOT / "notes/roadmaps/second-quantization-common-audit.md"
    text = replace_paths(path.read_text(encoding="utf-8"))
    if MARKER in text:
        return

    exposed_and_remaining = """## Bosonic specializations already exposed

The statistics-independent improvements identified by the original audit have now produced thin
Bosonic API where no new convergence argument is needed:

1. **Interaction-picture regularity.**
   `Bosonic.matrixCoeff_interactionPicture`, its continuity theorem, and its interval-integrability
   theorem directly specialize the Common finite-support proof; no finite configuration type is
   assumed.
2. **Algebraic free-evolution and quartic formulas.**
   The Bosonic API exposes Heisenberg-evolution composition together with interaction-picture formulas
   for quartic vertices and finite quartic interactions.
3. **Exchange and particle-number bridges.**
   The ordinary bosonic commutator is connected to `Common.exchangeCommutator`, and same-charge
   two-ladder diagonal coefficients vanish by the Common particle-number selection rule.

These additions are API specializations rather than duplicated proofs. They do not construct a
general bosonic Gibbs functional or a bosonic Dyson integral.

## Remaining nearly-free Bosonic candidates

1. **Summability-aware trace cyclicity.**
   `Common.tsumTrace_comp_comm` and related lemmas apply to arbitrary configuration types once the
   required double-series summability is supplied. Concrete Bosonic results should prove those
   hypotheses for a useful operator class rather than recreate the algebraic proof.
2. **Summability-aware KMS rotation.**
   The `tsumTrace` KMS path is already generic under explicit summability hypotheses. A public
   Bosonic theorem still needs the relevant Boltzmann-weight estimates and a clear operator domain.
3. **Additional quartic component aliases.**
   Common restriction, reassembly, decomposition, vertex-product, and sign-factorization results are
   statistics independent. New Bosonic names are worthwhile only where they make the public API
   easier to use; the proofs should remain in Common.

The main remaining Bosonic obstruction is analytic: arbitrary Gibbs expectations and operator-valued
Dyson integration need a convergence-aware domain. Algebraic and finite-support results should remain
independent of that larger construction.

"""
    text, count = re.subn(
        r"## Bosonic results that may later be nearly free\n.*?(?=## Physical source layout)",
        exposed_and_remaining,
        text,
        flags=re.DOTALL,
    )
    if count != 1:
        raise SystemExit("could not replace the Bosonic audit section")

    physical_layout = """## Physical source layout

The public responsibility umbrellas and physical source layout now agree wherever the internal
mathematics has the same boundary:

- `Common/{Algebra,ImaginaryTime,Thermal,Perturbation,Diagrammatics}/` contains the shared
  statistics-independent implementations;
- `Fermionic/{Algebra,ImaginaryTime,Thermal,Perturbation,Diagrammatics}/` contains the finite-mode
  fermionic implementations, with `QuantumLinkedCluster` classified under `Thermal/`;
- `Bosonic/{ImaginaryTime,Thermal,Diagrammatics}/` follows the same responsibility names, while the
  algebraic implementation intentionally keeps the finer `Foundations/` and `OperatorAlgebra/`
  split behind the public `Bosonic.Algebra` umbrella.

No compatibility shims remain at the former flat Common or Fermionic implementation paths. The
statistics-specific Bloch–de Dominicis specializations now live under each statistics' `Thermal/`
directory. Bosonic plain-namespace occupation/Fock aliases still exist as compatibility API, but
internal Bosonic code uses the canonical `SecondQuantization.Bosonic` names.

### Bloch–de Dominicis layout

The statistics-independent framework is under `Common/Thermal/BlochDeDominicis/` and is split by
mathematical role:

- `Unnormalized/` contains operator and trace peel identities before normalization;
- `GibbsExpectation/` contains the normalized functional and two-/four-point recursion;
- `Induction.lean` contains the arbitrary-length pairing theorem;
- `PairingWeight.lean` contains the statistics-dependent crossing weight.

Concrete specializations are colocated with the thermal APIs that discharge their hypotheses:

- `Bosonic/Thermal/BlochDeDominicis/TwoPoint.lean` supplies the uncutoff summability proof;
- `Fermionic/Thermal/BlochDeDominicis/TwoPoint.lean` supplies the finite-mode free two-point check;
- `Fermionic/Thermal/BlochDeDominicis/Examples/SingleMode.lean` records the algebraic four-point
  example for a normalized diagonal weight.

This separates the general recursion mechanism from the statistics-specific analytic or finite-basis
verification without pretending that the two concrete thermal theories have identical assumptions.
"""
    text, count = re.subn(r"## Physical source layout\n.*\Z", physical_layout, text, flags=re.DOTALL)
    if count != 1:
        raise SystemExit("could not replace the physical-layout audit section")
    write_if_changed(path, text)


def update_status() -> None:
    path = ROOT / "notes/roadmaps/second-quantization-status.md"
    text = replace_paths(path.read_text(encoding="utf-8"))

    anchor = """`SecondQuantization.Fermionic` imports all five fermionic umbrellas, while
`SecondQuantization.Bosonic` imports the four bosonic umbrellas. Smaller implementation modules remain
separate when they express a useful proof or dependency boundary; the layouts are not forced to have
identical file counts.
"""
    addition = anchor + """
The physical Fermionic directories now match the five umbrella responsibilities. Common follows the
same five-way layout. Bosonic keeps `Foundations/` and `OperatorAlgebra/` as a useful internal split
behind `Bosonic.Algebra`, while its imaginary-time, thermal, and diagrammatic implementations live
under the matching responsibility directories. Statistics-specific Bloch–de Dominicis files are
under `Bosonic/Thermal/BlochDeDominicis/` and `Fermionic/Thermal/BlochDeDominicis/`; the general
recursion remains under `Common/Thermal/BlochDeDominicis/`.
"""
    if "The physical Fermionic directories now match" not in text:
        if anchor not in text:
            raise SystemExit("could not find the status layout insertion point")
        text = text.replace(anchor, addition, 1)

    text = text.replace(
        "The extraction decisions and deferred Bosonic specializations are recorded in",
        "The extraction decisions, completed thin Bosonic specializations, and remaining analytic blockers are recorded in",
    )

    fermionic_intro = """- free imaginary-time evolution and arbitrary interaction-picture matrix coefficients
  (`Fermionic/ImaginaryTime/ImaginaryTimeEvolution.lean`, `Fermionic/ImaginaryTime/InteractionPicture.lean`);
"""
    if fermionic_intro in text and "occupation-cumulant bridge" not in text[text.index(fermionic_intro):text.index("## Bosonic line")]:
        text = text.replace(
            fermionic_intro,
            fermionic_intro
            + "- finite-basis thermal weights, partition/two-point functions, contractions, concrete Bloch–de Dominicis checks, and the occupation-cumulant bridge\n"
            + "  (`Fermionic/Thermal/`);\n",
            1,
        )

    write_if_changed(path, text)


def update_roadmap() -> None:
    path = ROOT / "notes/roadmaps/second-quantization.md"
    text = replace_paths(path.read_text(encoding="utf-8"))

    text = text.replace(
        "The bosonic line (`Bosonic/Foundations/Occupation.lean` onward) mirrors this shape one step behind, without the\nsign factors: see \"Bosonic line\" below.",
        "The bosonic line (`Bosonic/Foundations/Occupation.lean` onward) mirrors the algebraic and\ndiagrammatic responsibilities where the mathematics agrees, while its thermal and Dyson layers use\nseparate convergence-aware constructions: see \"Bosonic line\" below.",
    )

    text = text.replace(
        "| 8 | `Fermionic/Thermal/QuantumLinkedCluster.lean` / `Fermionic/Perturbation/FormalLogPartitionFunction.lean` — combinatorial linked-cluster groundwork: occupation-cumulant connectedness under a product weight, and `log Z` as a formal power series. Not yet the genuine (time-ordered, Wick-expanded) Linked Cluster Theorem — see below | `stated` (groundwork landed, see below) |",
        "| 8 | `Fermionic/Thermal/QuantumLinkedCluster.lean` / `Fermionic/Perturbation/FormalLogPartitionFunction.lean` — combinatorial linked-cluster groundwork: occupation-cumulant connectedness under a product weight, and `log Z` as a formal power series. Not yet the genuine (time-ordered, Wick-expanded) Linked Cluster Theorem — see below | `proved` groundwork; full LCT pending |",
    )
    text = text.replace(
        "| 9 | `Fermionic/ImaginaryTime/ImaginaryTimeEvolution.lean` — the algebraic, basis-diagonal realization of free imaginary-time evolution for the free Hamiltonian, and its Heisenberg-type conjugation of a general algebraic operator. First step of the finite-temperature Green-function / time-ordered-correlator line a genuine LCT needs | `stated` |",
        "| 9 | `Fermionic/ImaginaryTime/ImaginaryTimeEvolution.lean` — the algebraic, basis-diagonal realization of free imaginary-time evolution for the free Hamiltonian, and its Heisenberg-type conjugation of a general algebraic operator. First step of the finite-temperature Green-function / time-ordered-correlator line a genuine LCT needs | `proved` |",
    )

    old_interaction_note = """**Note on `interactionHamiltonian`:** the current `Σᵢⱼ V(i,j) Nᵢ Nⱼ` density-density form is
diagonal in the occupation-number basis (`interactionHamiltonian_basisState`) and hence commutes
with `freeHamiltonian`/`numberOperator` — too restrictive for a non-trivial Wick/Dyson expansion
later. A **general quartic fermionic interaction** target,
`Σᵢⱼₖₗ V(i,j,k,l) cᵢ† cⱼ† cₖ cₗ` (not basis-diagonal), is a separate future addition to this
phase, not yet started.
"""
    new_interaction_note = """**Note on interactions:** `Fermionic/Algebra/Hamiltonian.lean` still contains the diagonal
`Σᵢⱼ V(i,j) Nᵢ Nⱼ` density-density Hamiltonian. The non-diagonal quartic interaction needed for the
Wick/Dyson line is now implemented separately in
`Fermionic/Diagrammatics/QuarticInteraction.lean` as
`Σᵢⱼₖₗ V(i,j,k,l) cᵢ† cⱼ† cₖ cₗ`; the Dyson diagram expansion uses that general vertex rather than
the diagonal density-density operator.
"""
    if old_interaction_note in text:
        text = text.replace(old_interaction_note, new_interaction_note, 1)

    old_namespace = """The Fock-space and operator declarations (`basisState`, `create`,
`annihilate`, etc.) live under `namespace SecondQuantization.Bosonic`, distinct from the fermionic
line's plain `SecondQuantization` namespace, since those names all have fermionic namesakes;
`removeOccupation` is likewise namespaced there to avoid clashing with the fermionic occupation
API, while `Occupation`/`vacuum`/`createOccupation` remain in plain `SecondQuantization`.
"""
    new_namespace = """The canonical Fock-space and operator declarations (`Occupation`, `basisState`, `create`,
`annihilate`, etc.) live under `namespace SecondQuantization.Bosonic`, distinct from the fermionic
line's plain `SecondQuantization` namespace. Legacy plain-namespace occupation/Fock aliases remain
for compatibility, but the Bosonic implementation now uses only the canonical names internally.
"""
    if old_namespace in text:
        text = text.replace(old_namespace, new_namespace, 1)

    file_layout = """**File layout:** `SecondQuantization.Common`, `SecondQuantization.Fermionic`, and
`SecondQuantization.Bosonic` are the public aggregate imports. Common and Fermionic use matching
responsibility directories (`Algebra/`, `ImaginaryTime/`, `Thermal/`, `Perturbation/`, and
`Diagrammatics/`, with Bosonic omitting `Perturbation/`). Bosonic keeps a finer
`Foundations/`/`OperatorAlgebra/` split behind `Bosonic.Algebra` because that is a useful proof
boundary. `Fermionic/Thermal/QuantumLinkedCluster.lean` is exported by the Fermionic Thermal umbrella;
it is no longer a separate root import. Statistics-specific Bloch–de Dominicis checks live under
each statistics' `Thermal/BlochDeDominicis/` directory, while the general framework remains in
`Common/Thermal/BlochDeDominicis/`. The purely combinatorial pairing machinery lives upstream in
`Combinatorics/PerfectPairing.lean` and related files.

"""
    text, count = re.subn(
        r"\*\*File layout\*\*:.*?(?=The fermionic and bosonic lines proved the same shape of facts twice)",
        file_layout,
        text,
        flags=re.DOTALL,
    )
    if count != 1:
        raise SystemExit("could not replace the roadmap file-layout paragraph")

    old_retrofit = """**Retrofit done**: `Fermionic/Algebra/FockSpace.lean`/`Bosonic/Foundations/FockSpace.lean` define
`FockSpaceFermionic`/`FockSpaceBosonic` directly as `Common.AlgebraicFock (…)`; both
`Fermionic/ImaginaryTime/ImaginaryTimeEvolution.lean` and `Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean` define
`imaginaryTimeEvolveFree`/`imaginaryTimeEvolve` as `Common.diagonalEvolution`/`heisenbergEvolve`
specialized to their own real-valued eigenvalue. `totalNumberOperator`/`freeHamiltonian`/
`interactionHamiltonian` share `Common.diagonalOperator`.
"""
    new_retrofit = """**Retrofit done:** `Fermionic/Algebra/FockSpace.lean` and
`Bosonic/Foundations/FockSpace.lean` specialize `Common.AlgebraicFock`; the canonical bosonic type is
`SecondQuantization.Bosonic.FockSpace` (the old `FockSpaceBosonic` name is compatibility-only).
`Fermionic/ImaginaryTime/ImaginaryTimeEvolution.lean` and
`Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean` specialize `Common.diagonalEvolution` and
`Common.heisenbergEvolve`, while number operators and diagonal Hamiltonians share
`Common.diagonalOperator`.
"""
    if old_retrofit in text:
        text = text.replace(old_retrofit, new_retrofit, 1)

    # The historical PR list had become contradictory after component decomposition and scalar
    # prefactor factorization landed. Keep the history, but state the current boundary accurately.
    text = text.replace(
        "6. **Diagram connectedness — done through PR 6, PR 7 not started.** Built *before* any concrete",
        "6. **Diagram connectedness and component decomposition — complete through scalar-prefactor factorization.** Built *before* any concrete",
    )
    text, count = re.subn(
        r"    - \*\*PR 7 in progress, split into 7a/7b/7c\*\*:.*?coefficient bridge\.\n",
        """    - **PR 7 complete through component decomposition and scalar-prefactor factorization:**
      `Fermionic/Diagrammatics/WickDiagram/ComponentPartition.lean`, component restriction and
      connectedness, reassembly, the decomposition equivalence, and
      `AmplitudePrefactorFactorization.lean` establish the diagram-level component structure and
      factor the coupling/Dyson scalar prefactor. The remaining full-amplitude factorization is the
      ordered-simplex shuffle together with pairing-weight and pair-value compatibility under
      component-local orders; after that come the finite-set LCT and the `PowerSeries.log`
      coefficient bridge.
""",
        text,
        flags=re.DOTALL,
    )
    if count != 1:
        raise SystemExit("could not replace the roadmap PR 7 status block")

    # The old Common path predates the responsibility layout.
    text = text.replace(
        "`Common/Thermal/BlochDeDominicis/{TwoPoint,PeelFirst,PeelFirstTrace,PeelTermsIndexed,GibbsExpectation/Peel,GibbsExpectation/FourPoint}.lean`",
        "`Common/Thermal/BlochDeDominicis/{Unnormalized/TwoPoint,Unnormalized/PeelFirst,Unnormalized/PeelFirstTrace,Unnormalized/PeelTermsIndexed,GibbsExpectation/Peel,GibbsExpectation/FourPoint}.lean`",
    )
    text = text.replace(
        "`Common/Thermal/BlochDeDominicis/{TwoPoint,PeelFirst,PeelFirstTrace,PeelTermsIndexed,GibbsExpectation/Peel,GibbsExpectation/FourPoint,Induction}.lean`",
        "`Common/Thermal/BlochDeDominicis/{Unnormalized/TwoPoint,Unnormalized/PeelFirst,Unnormalized/PeelFirstTrace,Unnormalized/PeelTermsIndexed,GibbsExpectation/Peel,GibbsExpectation/FourPoint,Induction}.lean`",
    )

    write_if_changed(path, text)


def update_glossary() -> None:
    path = ROOT / "notes/glossary/second-quantization-terminology.md"
    text = replace_paths(path.read_text(encoding="utf-8"))
    text = text.replace(
        "| `Combinatorics/PerfectPairing.lean` | Determine the statistics-dependent pairing factor",
        "| `SecondQuantization/Common/Thermal/BlochDeDominicis/PairingWeight.lean` | Determine the statistics-dependent pairing factor",
    )
    text = text.replace(
        "| `SecondQuantization/Common/ImaginaryTime/TimeOrdering.lean` (fermionic consumers call it directly; `Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean` still fixes its own statistics) |",
        "| `SecondQuantization/Common/ImaginaryTime/TimeOrdering.lean` (fermionic consumers call it directly; the Bosonic imaginary-time layer fixes `Statistics.boson`) |",
    )
    text = text.replace("`FockSpaceBosonic`", "`Bosonic.FockSpace`")
    old_tail = """`Common/Algebra/AlgebraicFock.lean` correctly treats `matrixCoeff`/`diagonalCoeff` as coordinate evaluations rather than Hilbert-space matrix elements. `FormalLogPartitionFunction` correctly distinguishes its formal `log Z` power series from analytic exponentials and from the (now-proved) Dyson/linked-cluster theorem. `BlochDeDominicisPairing` already keeps pairings separate from contractions and expectations.
"""
    new_tail = """`Common/Algebra/AlgebraicFock.lean` correctly treats `matrixCoeff`/`diagonalCoeff` as coordinate evaluations rather than Hilbert-space matrix elements. `FormalLogPartitionFunction` correctly distinguishes its formal `log Z` power series from analytic exponentials; identifying its coefficients with connected Dyson diagrams remains part of the unfinished Linked Cluster Theorem. `Combinatorics/PerfectPairing.lean` and the Common Bloch–de Dominicis layer keep pairings separate from contractions and expectations.
"""
    if old_tail in text:
        text = text.replace(old_tail, new_tail, 1)
    write_if_changed(path, text)


def update_remaining_text_references() -> None:
    # Update exact physical file-path references in other Markdown and Lean documentation comments.
    primary = {
        ROOT / "notes/roadmaps/second-quantization-common-audit.md",
        ROOT / "notes/roadmaps/second-quantization-status.md",
        ROOT / "notes/roadmaps/second-quantization.md",
        ROOT / "notes/glossary/second-quantization-terminology.md",
    }
    candidates = list((ROOT / "notes").rglob("*.md")) + list((ROOT / "LeanCondensedMatter").rglob("*.lean"))
    for path in candidates:
        if path in primary:
            continue
        text = path.read_text(encoding="utf-8")
        updated = replace_paths(text)
        if updated != text:
            path.write_text(updated, encoding="utf-8")


def validate() -> None:
    audit = (ROOT / "notes/roadmaps/second-quantization-common-audit.md").read_text(encoding="utf-8")
    status = (ROOT / "notes/roadmaps/second-quantization-status.md").read_text(encoding="utf-8")
    roadmap = (ROOT / "notes/roadmaps/second-quantization.md").read_text(encoding="utf-8")
    glossary = (ROOT / "notes/glossary/second-quantization-terminology.md").read_text(encoding="utf-8")

    required = {
        "audit": (audit, MARKER),
        "status": (status, "Fermionic/Thermal/BlochDeDominicis/"),
        "roadmap": (roadmap, "Fermionic/Diagrammatics/WickDiagram/ComponentPartition.lean"),
        "glossary": (glossary, "SecondQuantization/Fermionic/Thermal/QuantumLinkedCluster.lean"),
    }
    for name, (text, needle) in required.items():
        if needle not in text:
            raise SystemExit(f"{name} is missing expected documentation: {needle}")

    forbidden = [
        "Fermionic/BlochDeDominicis/",
        "Bosonic/BlochDeDominicis/",
        "Fermionic/ImaginaryTimeEvolution.lean",
        "Fermionic/InteractionPicture.lean",
        "Fermionic/QuantumLinkedCluster.lean",
        "Fermionic/WickDiagram/",
        "Common/BlochDeDominicis/",
        "No Bosonic files are changed by this audit",
        "PR 7 not started",
        "PR 7 in progress",
    ]
    scan_paths = list((ROOT / "notes").rglob("*.md")) + list((ROOT / "LeanCondensedMatter").rglob("*.lean"))
    failures: list[str] = []
    for path in scan_paths:
        text = path.read_text(encoding="utf-8")
        for needle in forbidden:
            if needle in text:
                failures.append(f"{path.relative_to(ROOT)}: {needle}")
    if failures:
        raise SystemExit("stale second-quantization documentation remains:\n" + "\n".join(failures))


update_audit()
update_status()
update_roadmap()
update_glossary()
update_remaining_text_references()
validate()
print("Second-quantization documentation updated successfully.")
