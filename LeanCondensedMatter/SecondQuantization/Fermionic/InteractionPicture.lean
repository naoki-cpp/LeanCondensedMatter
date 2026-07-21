import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTimeEvolution

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# The interaction picture, and its matrix coefficients

Step 5 of Phase 9's Dyson-series plan (`notes/roadmaps/second-quantization.md`): the
interaction-picture operator `V_I(τ) := e^{τH₀} V e^{-τH₀}` for an arbitrary interaction operator
`V`, and the matrix-coefficient formula `dysonCoeff`'s recursion needs to establish continuity and
interval-integrability of `τ ↦ matrixCoeff (V_I τ) m n` before it can integrate against it.

`interactionPicture` is *not* a new construction — it is exactly `imaginaryTimeEvolve ε τ V`,
`ImaginaryTimeEvolution.lean`'s existing algebraic Heisenberg-type conjugation, applied to a
general (not necessarily eigenoperator) `V`. This file's contribution is the matrix-coefficient
formula and its continuity/integrability consequences, not a new operator.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The interaction-picture operator** `V_I(τ) := e^{τH₀} V e^{-τH₀}`, for an arbitrary
interaction operator `V` — not assumed to be an eigenoperator of the free evolution, unlike
`create`/`annihilate`. Exactly `imaginaryTimeEvolve ε τ V`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  imaginaryTimeEvolve ε τ V

omit [LinearOrder Mode] [Fintype Mode] in
/-- **At `τ = 0`, the interaction picture is trivial**: `V_I(0) = V`. -/
@[simp]
theorem interactionPicture_zero (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    interactionPicture ε V 0 = V :=
  imaginaryTimeEvolve_zero ε V

omit [LinearOrder Mode] in
/-- **The interaction-picture matrix-coefficient formula**: `V_I(τ)`'s `(m, n)` entry is `V`'s own
`(m, n)` entry, rescaled by `exp(τ(E(m) - E(n)))` — `Common.matrixCoeff_heisenbergEvolve`,
specialized to `fermionEnergy`. This is what lets `τ ↦ matrixCoeff (V_I τ) m n` be recognized as
continuous/interval-integrable below: it is a fixed complex constant times a real exponential of a
linear function of `τ`. -/
theorem matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ)
    (m n : FermionOccupation Mode) :
    Common.matrixCoeff (interactionPicture ε V τ) m n =
      Complex.exp ((τ * (fermionEnergy ε m - fermionEnergy ε n) : ℝ) : ℂ) *
        Common.matrixCoeff V m n :=
  Common.matrixCoeff_heisenbergEvolve (fermionEnergy ε) τ V m n

omit [LinearOrder Mode] in
/-- **Continuity in `τ`** of a single interaction-picture matrix coefficient, directly from the
closed-form `matrixCoeff_interactionPicture`: a constant times `Complex.exp` of a continuous
(affine) function of `τ`. -/
theorem continuous_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (m n : FermionOccupation Mode) :
    Continuous (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n) := by
  simp only [matrixCoeff_interactionPicture]
  fun_prop

omit [LinearOrder Mode] in
/-- **Interval-integrability in `τ`** of a single interaction-picture matrix coefficient, on any
interval — immediate from continuity. -/
theorem intervalIntegrable_matrixCoeff_interactionPicture (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (m n : FermionOccupation Mode)
    (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => Common.matrixCoeff (interactionPicture ε V τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_interactionPicture ε V m n).intervalIntegrable a b

end SecondQuantization
