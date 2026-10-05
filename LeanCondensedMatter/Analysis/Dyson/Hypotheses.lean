import LeanCondensedMatter.Analysis.Dyson.Basic

set_option linter.style.header false

/-!
# Bounded-interaction hypotheses for Dyson analysis

The generic Dyson estimates repeatedly use the same weak unit-norm assumption, nonnegative uniform
interaction bound, and compact-interval norm control.  This module owns that quantitative contract
and its continuous strengthening so downstream proofs cross one explicit analytic boundary without
requiring a stronger ambient norm typeclass.

The bound is only required on `[0, β]`.  No behavior outside that interval, and in particular no
negative-time bound, is encoded here.
-/

namespace Dyson

open Set

variable {A : Type*} [NormedRing A]

/-- Quantitative hypotheses for a bounded Dyson interaction on `[0, β]`.

The weak identity estimate `‖1‖ ≤ 1` is stored explicitly rather than requiring `NormOneClass`. -/
structure BoundedInteraction (V : ℝ → A) (β M : ℝ) : Prop where
  norm_one_le : ‖(1 : A)‖ ≤ 1
  bound_nonneg : 0 ≤ M
  interaction_norm_le : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M

/-- A bounded Dyson interaction together with the global continuity used by the Volterra theory. -/
structure ContinuousBoundedInteraction (V : ℝ → A) (β M : ℝ) : Prop
    extends BoundedInteraction V β M where
  interaction_continuous : Continuous V

/-- A continuous interaction on a nonnegative compact interval admits a uniform nonnegative bound.

The weak identity estimate is supplied explicitly so this does not require a stronger norm
typeclass. -/
theorem exists_continuousBoundedInteraction (V : ℝ → A) {β : ℝ}
    (hβ : 0 ≤ β) (hV : Continuous V) (hOne : ‖(1 : A)‖ ≤ 1) :
    ∃ M : ℝ, ContinuousBoundedInteraction V β M := by
  have hcont : Continuous (fun t : ℝ => ‖V t‖) := continuous_norm.comp hV
  obtain ⟨tmax, htmax, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hβ) hcont.continuousOn
  exact ⟨‖V tmax‖,
    { toBoundedInteraction :=
        { norm_one_le := hOne
          bound_nonneg := norm_nonneg _
          interaction_norm_le := fun t ht => hmax ht }
      interaction_continuous := hV }⟩

end Dyson
