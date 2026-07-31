import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

set_option linter.style.header false

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

noncomputable abbrev dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.dysonCoeff (fermionEnergy ε) V

omit [LinearOrder Mode] in
theorem dysonCoeff_zero (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ]
    FockSpaceFermionic Mode) (τ : ℝ) : dysonCoeff ε V 0 τ = LinearMap.id :=
  Common.dysonCoeff_zero (fermionEnergy ε) V τ

omit [LinearOrder Mode] in
theorem dysonCoeff_succ (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ]
    FockSpaceFermionic Mode) (n : ℕ) (τ : ℝ) : dysonCoeff ε V (n + 1) τ =
    - Common.operatorIntervalIntegral
      (fun σ => (interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) 0 τ :=
  Common.dysonCoeff_succ (fermionEnergy ε) V n τ

omit [LinearOrder Mode] in
theorem dysonCoeff_one (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ]
    FockSpaceFermionic Mode) (τ : ℝ) : dysonCoeff ε V 1 τ =
    - Common.operatorIntervalIntegral (interactionPicture ε V) 0 τ :=
  Common.dysonCoeff_one (fermionEnergy ε) V τ

omit [LinearOrder Mode] in
theorem dysonCoeff_at_zero (ε : Mode → ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ]
    FockSpaceFermionic Mode) (n : ℕ) : dysonCoeff ε V n 0 =
    if n = 0 then LinearMap.id else 0 := Common.dysonCoeff_at_zero (fermionEnergy ε) V n

omit [LinearOrder Mode] in
theorem matrixCoeff_dysonCoeff_succ (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) (τ : ℝ)
    (m n' : FermionOccupation Mode) : Common.matrixCoeff (dysonCoeff ε V (n + 1) τ) m n' =
    - ∫ σ in (0 : ℝ)..τ, ∑ k : FermionOccupation Mode,
      Common.matrixCoeff (interactionPicture ε V σ) m k *
        Common.matrixCoeff (dysonCoeff ε V n σ) k n' :=
  Common.matrixCoeff_dysonCoeff_succ (fermionEnergy ε) V n τ m n'

omit [LinearOrder Mode] in
theorem continuous_matrixCoeff_dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    ∀ m n' : FermionOccupation Mode,
      Continuous (fun τ : ℝ => Common.matrixCoeff (dysonCoeff ε V n τ) m n') :=
  Common.continuous_matrixCoeff_dysonCoeff (fermionEnergy ε) V n

omit [LinearOrder Mode] in
theorem intervalIntegrable_matrixCoeff_dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ)
    (m n' : FermionOccupation Mode) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => Common.matrixCoeff (dysonCoeff ε V n τ) m n')
      MeasureTheory.volume a b :=
  Common.intervalIntegrable_matrixCoeff_dysonCoeff (fermionEnergy ε) V n m n' a b

noncomputable abbrev dysonTruncation (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :=
  Common.dysonTruncation (fermionEnergy ε) V

end SecondQuantization
