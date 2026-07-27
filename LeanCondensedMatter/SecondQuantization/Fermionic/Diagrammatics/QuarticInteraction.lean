import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.VertexLabel

set_option linter.style.header false

/-!
# A fixed-arity number-conserving quartic interaction

Step 6 (PR 3) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): the
first *concrete* interaction operator a Wick diagram can be extracted from. Unlike the existing
`interactionHamiltonian` (basis-diagonal, hence commuting with `freeHamiltonian` and physically too
restrictive for a non-trivial Dyson expansion), `quarticInteraction` is a genuine, generally
non-diagonal number-conserving quartic vertex `Σ g(q) cᵢ†cⱼ†cₗck` — not yet the density-density
special case, and deliberately not yet the arbitrary operator `dysonCoeff` is stated for (an
arbitrary linear map carries no vertex/leg/mode information a diagram could be extracted from).

**Deliberately not included in this PR**, per the diagram-connectedness plan (later PRs, or
separate predicates, add these on top rather than baking them into the type):
- Hermiticity of the coupling `g`
- antisymmetry of `g` under the two creation/two annihilation index swaps
- any `1/2`/`1/4!` combinatorial prefactor
- momentum/quantum-number conservation constraints on `g`
- variable-arity or bosonic generalizations

**Operator ordering convention, fixed here and used throughout the rest of this plan**:
`quarticVertexOperator q := c_{q.create₁}† c_{q.create₂}† c_{q.annihilate₂} c_{q.annihilate₁}`,
i.e. both creation operators first (in index order `create₁`, `create₂`), then both annihilation
operators (in *reverse* index order, `annihilate₂` then `annihilate₁`) — matching the physics
reference notes' `c_i† c_j† c_l c_k` convention for a vertex labelled `(i, j, k, l)`.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- Compatibility alias for the statistics-independent quartic vertex label. -/
abbrev QuarticVertexLabel (Mode : Type*) := Common.QuarticVertexLabel Mode

/-- **The quartic vertex operator**, `c_{q.create₁}† c_{q.create₂}† c_{q.annihilate₂}
c_{q.annihilate₁}` — see the module docstring for why this specific operator order is fixed. -/
noncomputable def quarticVertexOperator (q : QuarticVertexLabel Mode) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  (create q.create₁).comp
    ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁)))

/-- **The quartic interaction**, `Σ_q g(q) • quarticVertexOperator q` — a genuine, generally
non-diagonal number-conserving quartic interaction, for an arbitrary coupling `g`. -/
noncomputable def quarticInteraction (g : QuarticVertexLabel Mode → ℂ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ∑ q, g q • quarticVertexOperator q

omit [Fintype Mode] in
/-- **A single quartic vertex's interaction-picture expansion**: at time `τ`, it is the same
vertex operator, rescaled by `exp(τ(ε(create₁) + ε(create₂) - ε(annihilate₁) - ε(annihilate₂)))`
— each of its four ladder operators evolves independently (`imaginaryTimeEvolve_create`/
`_annihilate`) and `heisenbergEvolve_comp` distributes the conjugation across their composition,
collecting one exponential factor per leg. -/
theorem interactionPicture_quarticVertexOperator (ε : Mode → ℝ) (q : QuarticVertexLabel Mode)
    (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      Complex.exp (((τ : ℂ)) * ((ε q.create₁ : ℂ) + (ε q.create₂ : ℂ) - (ε q.annihilate₁ : ℂ) -
        (ε q.annihilate₂ : ℂ))) • quarticVertexOperator q := by
  change imaginaryTimeEvolve ε τ (quarticVertexOperator q) = _
  have hcomp : imaginaryTimeEvolve ε τ (quarticVertexOperator q) =
      (imaginaryTimeEvolve ε τ (create q.create₁)).comp
        ((imaginaryTimeEvolve ε τ (create q.create₂)).comp
          ((imaginaryTimeEvolve ε τ (annihilate q.annihilate₂)).comp
            (imaginaryTimeEvolve ε τ (annihilate q.annihilate₁)))) := by
    simp only [quarticVertexOperator, imaginaryTimeEvolve, Common.heisenbergEvolve_comp]
  rw [hcomp, imaginaryTimeEvolve_create, imaginaryTimeEvolve_create, imaginaryTimeEvolve_annihilate,
    imaginaryTimeEvolve_annihilate]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [show (create q.create₁).comp
      ((create q.create₂).comp ((annihilate q.annihilate₂).comp (annihilate q.annihilate₁))) =
      quarticVertexOperator q from rfl]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- **The quartic interaction's interaction-picture expansion**: `V_I(τ)` is the sum, over every
vertex `q`, of the same coupling `g q` times its own `interactionPicture_quarticVertexOperator`
expansion — the linearity of `interactionPicture` (as `imaginaryTimeEvolve`/`heisenbergEvolve`)
applied to `quarticInteraction`'s defining `Finset.sum`. -/
theorem interactionPicture_quarticInteraction (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ : ℝ) :
    interactionPicture ε (quarticInteraction g) τ =
      ∑ q, g q • interactionPicture ε (quarticVertexOperator q) τ := by
  change imaginaryTimeEvolve ε τ (quarticInteraction g) = _
  rw [quarticInteraction]
  change Common.heisenbergEvolve (fermionEnergy ε) τ (∑ q, g q • quarticVertexOperator q) = _
  rw [Common.heisenbergEvolve_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Common.heisenbergEvolve_smul]
  rfl

end SecondQuantization
