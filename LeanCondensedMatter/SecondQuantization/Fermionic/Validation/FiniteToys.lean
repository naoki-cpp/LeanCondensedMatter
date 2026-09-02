import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StaticStredaWardBridge

set_option linter.style.header false

/-!
# Finite transport toy models

This module begins the validation layer for the clean finite Kubo–Středa chain. It keeps the toy
models separate from the general theorems and introduces:

* a concrete two-level Hilbert space with a degenerate zero Hamiltonian;
* its canonical finite pure-point basis and uniform diagonal state;
* independently supplied zero and scalar current operators;
* zero-current and simultaneous-current-sign symmetry checks for the canonical Bastin trace; and
* a nontrivial two-site Hermitian dimer hopping model.

The pointwise Bastin/Středa equality below is an instantiation of the general theorem, while the
zero-current and sign-reversal statements are symbolic sanity checks on the concrete conventions.
No numerical approximation, disorder average, or limiting statement occurs here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open _root_.SecondQuantization.Fermionic.Lattice Transport

open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

/-- Canonical Hilbert basis of the concrete two-level space. -/
noncomputable def twoLevelBasis : HilbertBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis

/-- Degenerate two-level free system with `H = 0` and `ℏ = 1`. -/
noncomputable def twoLevelSystem : BoundedFreeSystem (EuclideanSpace ℂ (Fin 2)) where
  hamiltonian := ⟨0, by simp⟩
  hbar := 1
  hbar_pos := by norm_num

/-- Uniform pure-point state on the degenerate two-level basis. -/
noncomputable def twoLevelData : PurePointLehmannData twoLevelSystem (Fin 2) where
  basis := twoLevelBasis
  energy := fun _ => 0
  hamiltonian_apply_basis := by
    intro i
    simp [twoLevelSystem]
  probability := fun _ => (1 : ℝ) / 2
  probability_nonneg := by
    intro i
    norm_num
  probability_summable := Summable.of_finite
  probability_tsum := by
    rw [tsum_fintype]
    norm_num [Fin.sum_univ_two]

@[simp]
theorem twoLevelData_energy (i : Fin 2) :
    twoLevelData.energy i = 0 :=
  rfl

@[simp]
theorem twoLevelData_probability (i : Fin 2) :
    twoLevelData.probability i = (1 : ℝ) / 2 :=
  rfl

/-- The two levels are degenerate and carry equal probabilities. -/
theorem twoLevel_probability_symmetry :
    twoLevelData.probability 0 = twoLevelData.probability 1 :=
  rfl

/-- Independently supplied zero current on the two-level space. -/
def twoLevelZeroCurrent :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  0

/-- Independently supplied scalar current on the two-level space. -/
def twoLevelScalarCurrent :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  1

@[simp]
theorem twoLevelScalarCurrent_apply (ψ : EuclideanSpace ℂ (Fin 2)) :
    twoLevelScalarCurrent ψ = ψ := by
  simp [twoLevelScalarCurrent]

/-- Simultaneously reversing both supplied currents leaves the canonical Bastin operator integrand
unchanged. This is a symbolic bilinearity/sign sanity check independent of the toy Hamiltonian. -/
theorem regularizedBastinOperatorIntegrand_neg_neg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) :
    regularizedBastinOperatorIntegrand
        hamiltonian (-current₁) (-current₂) energy broadening =
      regularizedBastinOperatorIntegrand
        hamiltonian current₁ current₂ energy broadening := by
  unfold regularizedBastinOperatorIntegrand
  noncomm_ring

/-- The same simultaneous-current-sign symmetry after taking the ordinary finite-dimensional
trace. -/
theorem regularizedBastinTraceIntegrand_neg_neg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    (hamiltonian current₁ current₂ : H →L[ℂ] H)
    (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        hamiltonian (-current₁) (-current₂) energy broadening =
      regularizedBastinTraceIntegrand
        hamiltonian current₁ current₂ energy broadening := by
  unfold regularizedBastinTraceIntegrand
  rw [regularizedBastinOperatorIntegrand_neg_neg]

/-- A vanishing first current makes the canonical two-level Bastin trace vanish. -/
theorem twoLevel_zeroCurrent_bastinTrace_zero
    (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        twoLevelSystem.hamiltonian.1
        twoLevelZeroCurrent twoLevelScalarCurrent energy broadening = 0 := by
  simp [regularizedBastinTraceIntegrand, regularizedBastinOperatorIntegrand,
    twoLevelZeroCurrent]

/-- Consequently, the corresponding pointwise Středa surface-derivative plus residual-sea trace
also vanishes. -/
theorem twoLevel_zeroCurrent_streda_sum_zero
    (energy broadening : ℝ) :
    regularizedStredaSurfacePrimitiveTraceDerivative
        twoLevelSystem.hamiltonian.1
        twoLevelZeroCurrent twoLevelScalarCurrent energy broadening +
      regularizedStredaResidualSeaTraceKernel
        twoLevelSystem.hamiltonian.1
        twoLevelZeroCurrent twoLevelScalarCurrent energy broadening = 0 := by
  rw [← regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea]
  exact twoLevel_zeroCurrent_bastinTrace_zero energy broadening

/-- Concrete pointwise Kubo–Bastin/Středa agreement for the scalar-current two-level toy model. -/
theorem twoLevel_scalarCurrent_bastin_eq_streda
    (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        twoLevelSystem.hamiltonian.1
        twoLevelScalarCurrent twoLevelScalarCurrent energy broadening =
      regularizedStredaSurfacePrimitiveTraceDerivative
          twoLevelSystem.hamiltonian.1
          twoLevelScalarCurrent twoLevelScalarCurrent energy broadening +
        regularizedStredaResidualSeaTraceKernel
          twoLevelSystem.hamiltonian.1
          twoLevelScalarCurrent twoLevelScalarCurrent energy broadening :=
  regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea
    twoLevelSystem.hamiltonian.1
    twoLevelScalarCurrent twoLevelScalarCurrent energy broadening

/-- Simultaneous reversal of the scalar current leaves the concrete two-level Bastin trace
unchanged. -/
theorem twoLevel_scalarCurrent_sign_symmetry
    (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        twoLevelSystem.hamiltonian.1
        (-twoLevelScalarCurrent) (-twoLevelScalarCurrent) energy broadening =
      regularizedBastinTraceIntegrand
        twoLevelSystem.hamiltonian.1
        twoLevelScalarCurrent twoLevelScalarCurrent energy broadening :=
  regularizedBastinTraceIntegrand_neg_neg
    twoLevelSystem.hamiltonian.1
    twoLevelScalarCurrent twoLevelScalarCurrent energy broadening

/-- Two-site type used by the finite tight-binding dimer validation. -/
abbrev TwoSite := Fin 2

/-- Hermitian two-site dimer hopping with oriented amplitudes `t` and `star t` and no on-site
terms. -/
noncomputable def twoSiteDimerHopping (t : ℂ) : LocallyFiniteHopping TwoSite where
  column y := if y = 0 then Finsupp.single 1 t else Finsupp.single 0 (star t)
  incident _ := Finset.univ
  self_mem := by simp
  outside_incident := by
    intro x y hy
    simp at hy

@[simp]
theorem twoSiteDimerHopping_column_zero_one (t : ℂ) :
    ((twoSiteDimerHopping t).column 0) 1 = t := by
  simp [twoSiteDimerHopping]

@[simp]
theorem twoSiteDimerHopping_column_one_zero (t : ℂ) :
    ((twoSiteDimerHopping t).column 1) 0 = star t := by
  simp [twoSiteDimerHopping]

@[simp]
theorem twoSiteDimerHopping_column_zero_zero (t : ℂ) :
    ((twoSiteDimerHopping t).column 0) 0 = 0 := by
  simp [twoSiteDimerHopping]

@[simp]
theorem twoSiteDimerHopping_column_one_one (t : ℂ) :
    ((twoSiteDimerHopping t).column 1) 1 = 0 := by
  simp [twoSiteDimerHopping]

/-- The two oriented hopping amplitudes are Hermitian conjugates. -/
theorem twoSiteDimerHopping_hermitian_pair (t : ℂ) :
    star ((twoSiteDimerHopping t).amplitude 1 0) =
      (twoSiteDimerHopping t).amplitude 0 1 := by
  simp [LocallyFiniteHopping.amplitude_eq]

end
end Validation
end Fermionic
end SecondQuantization
