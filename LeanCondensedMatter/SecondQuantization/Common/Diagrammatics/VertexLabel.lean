import Mathlib

set_option linter.style.header false

/-!
# Quartic vertex labels

A quartic interaction vertex carries two creation modes and two annihilation modes. This data is
independent of particle statistics; fermionic and bosonic operator layers provide their own concrete
interpretations of the shared label.
-/

namespace SecondQuantization
namespace Common

/-- The four mode labels of a number-conserving quartic interaction vertex. -/
structure QuarticVertexLabel (Mode : Type*) where
  /-- The first creation mode. -/
  create₁ : Mode
  /-- The second creation mode. -/
  create₂ : Mode
  /-- The first annihilation mode. -/
  annihilate₁ : Mode
  /-- The second annihilation mode. -/
  annihilate₂ : Mode
  deriving DecidableEq, Fintype

end Common
end SecondQuantization
