import LeanCondensedMatter.Analysis.Operator.Unbounded.Composition
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Ladder
import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic

set_option linter.style.header false

/-!
# Completed bosonic quartic vertices

This file gives the ordered number-conserving quartic monomial

`a†_{create₁} a†_{create₂} a_{annihilate₂} a_{annihilate₁}`

a genuine meaning on completed bosonic Fock space.  The four unbounded ladder operators are composed
with the exact `LinearPMap.comp` domain at every stage, so no operator product is formed outside the
domain on which the preceding result lies in the next operator's domain.

This is the first completed-space interacting operator.  The present file deliberately does not
replace the exact composition domain by a closed-form weighted `ℓ²` description, nor does it yet
form finite sums of quartic vertices.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- The ordered bosonic quartic vertex as a partially defined linear operator on completed Fock
space.  Its domain is the exact iterated composition domain of the four ladder operators. -/
noncomputable def completedQuarticVertexOperator (q : Common.QuarticVertexLabel Mode) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  (completedCreate q.create₁).comp
    ((completedCreate q.create₂).comp
      ((completedAnnihilate q.annihilate₂).comp
        (completedAnnihilate q.annihilate₁)))

end
end Bosonic
end SecondQuantization
