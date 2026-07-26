import Mathlib

set_option linter.style.header false

/-!
# Quartic vertex labels

A `QuarticVertexLabel Mode` records the modes of two creation and two annihilation legs. The label
contains no operator algebra, exchange sign, or particle statistics, so it can be shared by the
bosonic and fermionic developments.
-/

namespace SecondQuantization
namespace Common

/-- A quartic interaction vertex's mode label: two creation modes and two annihilation modes. -/
structure QuarticVertexLabel (Mode : Type*) where
  /-- The first creation operator's mode. -/
  create₁ : Mode
  /-- The second creation operator's mode. -/
  create₂ : Mode
  /-- The first annihilation operator's mode. -/
  annihilate₁ : Mode
  /-- The second annihilation operator's mode. -/
  annihilate₂ : Mode
  deriving DecidableEq, Fintype

end Common
end SecondQuantization
