from pathlib import Path
import subprocess

root = Path.cwd()
base = root / 'LeanCondensedMatter/SecondQuantization/Common'

moves = {
    'OneParticleSpace.lean': 'Algebra/OneParticleSpace.lean',
    'Statistics.lean': 'Algebra/Statistics.lean',
    'OccupationBasis.lean': 'Algebra/OccupationBasis.lean',
    'AlgebraicFock.lean': 'Algebra/AlgebraicFock.lean',
    'ParticleNumberSelectionRule.lean': 'Algebra/ParticleNumberSelectionRule.lean',
    'ExchangeCommutator.lean': 'Algebra/ExchangeCommutator.lean',
    'ExchangeAlgebra.lean': 'Algebra/ExchangeAlgebra.lean',
    'TimeOrdering.lean': 'ImaginaryTime/TimeOrdering.lean',
    'DiagonalEvolution.lean': 'ImaginaryTime/DiagonalEvolution.lean',
    'InteractionPicture.lean': 'ImaginaryTime/InteractionPicture.lean',
    'KMSRotation.lean': 'ImaginaryTime/KMSRotation.lean',
    'NormalizedOperatorFunctional.lean': 'Thermal/NormalizedOperatorFunctional.lean',
    'WeightedDiagonalFunctional.lean': 'Thermal/WeightedDiagonalFunctional.lean',
    'BlochDeDominicis.lean': 'Thermal/BlochDeDominicis.lean',
    'BlochDeDominicis/PairingWeight.lean': 'Thermal/BlochDeDominicis/PairingWeight.lean',
    'BlochDeDominicis/TwoPoint.lean': 'Thermal/BlochDeDominicis/Unnormalized/TwoPoint.lean',
    'BlochDeDominicis/PeelFirst.lean': 'Thermal/BlochDeDominicis/Unnormalized/PeelFirst.lean',
    'BlochDeDominicis/PeelFirstTrace.lean': 'Thermal/BlochDeDominicis/Unnormalized/PeelFirstTrace.lean',
    'BlochDeDominicis/PeelTermsIndexed.lean': 'Thermal/BlochDeDominicis/Unnormalized/PeelTermsIndexed.lean',
    'BlochDeDominicis/Specializations/FourPointReduction.lean': 'Thermal/BlochDeDominicis/Unnormalized/FourPointReduction.lean',
    'BlochDeDominicis/GibbsExpectation.lean': 'Thermal/BlochDeDominicis/GibbsExpectation.lean',
    'BlochDeDominicis/GibbsExpectation/Core.lean': 'Thermal/BlochDeDominicis/GibbsExpectation/Core.lean',
    'BlochDeDominicis/GibbsExpectation/TwoPoint.lean': 'Thermal/BlochDeDominicis/GibbsExpectation/TwoPoint.lean',
    'BlochDeDominicis/GibbsExpectation/Peel.lean': 'Thermal/BlochDeDominicis/GibbsExpectation/Peel.lean',
    'BlochDeDominicis/GibbsExpectation/FourPoint.lean': 'Thermal/BlochDeDominicis/GibbsExpectation/FourPoint.lean',
    'BlochDeDominicis/Induction.lean': 'Thermal/BlochDeDominicis/Induction.lean',
    'FiniteOperatorIntegral.lean': 'Perturbation/FiniteOperatorIntegral.lean',
    'QuarticVertexLabel.lean': 'Diagrammatics/VertexLabel.lean',
    'QuarticLeg.lean': 'Diagrammatics/Leg.lean',
    'QuarticDiagram.lean': 'Diagrammatics/Diagram.lean',
    'QuarticDiagramOrdered.lean': 'Diagrammatics/Ordered.lean',
    'QuarticDiagramConnected.lean': 'Diagrammatics/Connected.lean',
    'QuarticDiagramComponentPartition.lean': 'Diagrammatics/ComponentPartition.lean',
    'QuarticDiagramComponentRestriction.lean': 'Diagrammatics/ComponentRestriction.lean',
    'QuarticDiagramComponentVertexProduct.lean': 'Diagrammatics/ComponentVertexProduct.lean',
    'QuarticDiagramComponentConnected.lean': 'Diagrammatics/ComponentConnected.lean',
    'QuarticDiagramReassemble.lean': 'Diagrammatics/Reassemble.lean',
    'QuarticDiagramReassembleComponentPartitionEq.lean': 'Diagrammatics/ReassembleComponentPartitionEq.lean',
    'QuarticDiagramReassembleRestrictComponent.lean': 'Diagrammatics/ReassembleRestrictComponent.lean',
    'QuarticDiagramReassembleDecompose.lean': 'Diagrammatics/ReassembleDecompose.lean',
    'QuarticDiagramComponentDecompositionEquiv.lean': 'Diagrammatics/ComponentDecompositionEquiv.lean',
}

module_repl = {}
doc_repl = {}
for old, new in moves.items():
    module_repl['LeanCondensedMatter.SecondQuantization.Common.' + old[:-5].replace('/', '.')] = (
        'LeanCondensedMatter.SecondQuantization.Common.' + new[:-5].replace('/', '.'))
    doc_repl['Common/' + old] = 'Common/' + new

for old, new in moves.items():
    src, dst = base / old, base / new
    dst.parent.mkdir(parents=True, exist_ok=True)
    if src.exists():
        if dst.exists():
            if src.read_bytes() != dst.read_bytes():
                raise RuntimeError(f'conflicting destination: {old} -> {new}')
            src.unlink()
        else:
            src.rename(dst)
    elif not dst.exists():
        raise FileNotFoundError(old)

for p in root.rglob('*'):
    if not p.is_file() or p.suffix not in {'.lean', '.md', '.yml', '.yaml'}:
        continue
    text = p.read_text(encoding='utf-8')
    original = text
    for old, new in sorted(module_repl.items(), key=lambda item: -len(item[0])):
        text = text.replace(old, new)
    for old, new in sorted(doc_repl.items(), key=lambda item: -len(item[0])):
        text = text.replace(old, new)
    if text != original:
        p.write_text(text, encoding='utf-8')

(base / 'Thermal/BlochDeDominicis/Unnormalized.lean').write_text('''import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelTermsIndexed
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.FourPointReduction

set_option linter.style.header false

/-!
# Unnormalized Bloch–de Dominicis recursion

Operator and trace identities that peel the first field from an ordered product before normalization
by a Gibbs partition function. The normalized expectation-value layer is kept separately under
`GibbsExpectation/`.
-/
''', encoding='utf-8')

(base / 'Thermal/BlochDeDominicis.lean').write_text('''import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Bloch–de Dominicis theorem

The shared finite-temperature pairing theory is organized into three layers:

- `Unnormalized`: operator/trace peel identities before division by the partition function;
- `GibbsExpectation`: normalized Gibbs functionals and their two-/four-point recursion lemmas;
- `Induction`: the arbitrary-length pairing theorem.

`PairingWeight` supplies the statistics-dependent crossing factor used by the final expansion.
-/
''', encoding='utf-8')

umbrellas = {
'Algebra.lean': '''import LeanCondensedMatter.SecondQuantization.Common.Algebra.OneParticleSpace
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics
import LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ParticleNumberSelectionRule
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeCommutator
import LeanCondensedMatter.SecondQuantization.Common.Algebra.ExchangeAlgebra

set_option linter.style.header false

/-!
# Statistics-independent second-quantization algebra

One-particle labels, particle statistics, occupation-basis interfaces, algebraic Fock spaces,
particle-number selection rules, and the common CAR/CCR exchange-algebra interface.
-/
''',
'ImaginaryTime.lean': '''import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.KMSRotation

set_option linter.style.header false

/-!
# Statistics-independent imaginary-time infrastructure

Statistics-aware time ordering, basis-diagonal free evolution, algebraic Heisenberg evolution,
interaction-picture operators, and KMS rotation identities.
-/
''',
'Thermal.lean': '''import LeanCondensedMatter.SecondQuantization.Common.Thermal.NormalizedOperatorFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis

set_option linter.style.header false

/-!
# Statistics-independent thermal functionals and pairing expansions

Normalized operator functionals, finite and summability-aware diagonal traces, Gibbs
specializations, and the abstract Bloch–de Dominicis pairing theorem.
-/
''',
'Perturbation.lean': '''import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# Finite-basis perturbative infrastructure

Coefficientwise interval integration of endomorphism-valued functions on a finite occupation basis.
This is kept separate because the present reconstruction of an operator from all matrix coefficients
requires a finite configuration type; a convergence-aware bosonic analogue is not yet available.
-/
''',
'Diagrammatics.lean': '''import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.VertexLabel
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Leg
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Connected
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentConnected
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Reassemble
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ReassembleComponentPartitionEq
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ReassembleRestrictComponent
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ReassembleDecompose
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentDecompositionEquiv

set_option linter.style.header false

/-!
# Statistics-independent quartic diagrammatics

Quartic vertex labels and leg indexing, ordered diagram data, connected components, component
restriction and reassembly, decomposition equivalences, and componentwise scalar factorization.
-/
'''
}
for name, content in umbrellas.items():
    (base / name).write_text(content, encoding='utf-8')

audit = root / 'notes/roadmaps/second-quantization-common-audit.md'
text = audit.read_text(encoding='utf-8')
if '## Physical source layout' not in text:
    text += '''
## Physical source layout

The responsibility umbrellas now match the physical directory layout:

- `Common/Algebra/` — basis-independent algebraic Fock and exchange infrastructure;
- `Common/ImaginaryTime/` — time ordering, diagonal evolution, interaction picture, and KMS rotation;
- `Common/Thermal/` — normalized/weighted functionals and Bloch–de Dominicis;
- `Common/Perturbation/` — finite-basis operator integration;
- `Common/Diagrammatics/` — quartic diagram data and component decomposition.

No compatibility shims remain at the old flat `Common/*.lean` implementation paths. The only
root-level files under `Common/` are the five public responsibility umbrellas.

### Bloch–de Dominicis internal layout

`Common/Thermal/BlochDeDominicis/` is split by mathematical role rather than theorem length:

- `Unnormalized/` contains operator and trace peel identities before normalization;
- `GibbsExpectation/` contains the normalized functional and two-/four-point recursion;
- `Induction.lean` contains the arbitrary-length pairing theorem;
- `PairingWeight.lean` contains the statistics-dependent crossing weight.

This keeps the recursion mechanism visible without mixing it with the normalization layer.
'''
    audit.write_text(text, encoding='utf-8')

status = root / 'notes/roadmaps/second-quantization-status.md'
text = status.read_text(encoding='utf-8')
text = text.replace(
    'The following infrastructure is shared by both statistics:',
    'The following infrastructure is shared by both statistics. The listed modules live under the matching `Common/Algebra/`, `Common/ImaginaryTime/`, `Common/Thermal/`, or `Common/Diagrammatics/` directory:')
status.write_text(text, encoding='utf-8')

Path('.github/scripts/refactor_common_layout.py').unlink()
workflow = subprocess.check_output(
    ['git', 'show', 'origin/main:.github/workflows/lean_action_ci.yml'], text=True)
Path('.github/workflows/lean_action_ci.yml').write_text(workflow, encoding='utf-8')
