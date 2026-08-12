import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition

set_option linter.style.header false

/-!
# Interaction slots of the external component

The linked-cluster development repeatedly needs the interaction slots carried by the canonical
external component.  The mathematical owner of that set is the Common two-point component
decomposition; this Fermionic declaration is only the diagram-specific name used by the external
piece construction.

The former mixed-position external/vacuum splitting lived in this module as well.  That route was a
binary reimplementation of the existing component factorization and has been removed: pairing and
amplitude factorization now have a single authoritative component-wise route.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- The interaction slots belonging to the canonical external component. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalSlots
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j) : Finset (Fin n) :=
  Common.TwoPointDiagram.interactionPart
    (d.1.externalComponentPart : Finset (Common.TwoPointVertex (Finset.univ : Finset (Fin n))))

end Fermionic
end SecondQuantization
