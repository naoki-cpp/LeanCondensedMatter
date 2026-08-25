import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.TwoPoint

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# Convergence-aware bosonic Gibbs functionals

A bosonic occupation space is infinite even when the mode type is finite.  A Gibbs expectation on
algebraic Fock-space endomorphisms therefore cannot be presented as an unrestricted finite weighted
sum.  This module records the smallest partial-linear interface needed by the perturbative thermal
line:

- an explicit submodule of observables whose Gibbs numerator is summable;
- a linear expectation on that submodule;
- a distinguished unit observable with normalized expectation;
- the canonical free-boson realization under `0 < β ε i`.

No boundedness, trace-class, or completed-Fock-space claim is made here.  Those analytic upgrades
belong to the completed representation and domain program.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

/-- A normalized Gibbs functional defined on an explicit linear domain of admissible observables.

The domain is a `Submodule`, so closure under finite linear combinations is part of the data.  Any
additional closure under operator products or integrals must be supplied separately by the theorem
that uses those operations. -/
structure ConvergenceAwareGibbsFunctional (Observable : Type*)
    [AddCommMonoid Observable] [Module ℂ Observable] where
  /-- Observables for which the expectation is analytically defined. -/
  domain : Submodule ℂ Observable
  /-- The linear expectation on the admissible domain. -/
  expectation : domain →ₗ[ℂ] ℂ
  /-- The observable representing the empty product. -/
  unit : Observable
  /-- The empty-product observable belongs to the analytic domain. -/
  unit_mem : unit ∈ domain
  /-- The expectation is normalized on the empty product. -/
  expectation_unit : expectation ⟨unit, unit_mem⟩ = 1

namespace ConvergenceAwareGibbsFunctional

variable {Observable : Type*} [AddCommMonoid Observable] [Module ℂ Observable]

/-- Totalize a partial Gibbs functional by assigning zero outside its stated analytic domain.

All physical theorems using `value` must separately provide domain membership.  The totalization is
only an adapter to APIs, such as `ExpectationPairingRecursion`, whose expectation field is total. -/
noncomputable def value (functional : ConvergenceAwareGibbsFunctional Observable)
    (A : Observable) : ℂ := by
  classical
  exact if hA : A ∈ functional.domain then functional.expectation ⟨A, hA⟩ else 0

/-- On an admissible observable, the totalized value is the underlying partial expectation. -/
theorem value_of_mem (functional : ConvergenceAwareGibbsFunctional Observable)
    {A : Observable} (hA : A ∈ functional.domain) :
    functional.value A = functional.expectation ⟨A, hA⟩ := by
  classical
  simp [value, hA]

/-- The totalized functional remains normalized on its distinguished unit. -/
@[simp]
theorem value_unit (functional : ConvergenceAwareGibbsFunctional Observable) :
    functional.value functional.unit = 1 := by
  rw [functional.value_of_mem functional.unit_mem]
  exact functional.expectation_unit

end ConvergenceAwareGibbsFunctional

variable {Mode : Type*} [Fintype Mode]

/-- Explicit summability condition for a free bosonic Gibbs numerator.

For an algebraic-Fock endomorphism `A`, this is absolute summability of the diagonal coefficients of
`e^{-βH₀} A` over the genuinely infinite occupation type. -/
noncomputable def freeGibbsSummable (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) : Prop :=
  Summable (fun n : Occupation Mode =>
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp A) n n)

/-- The linear domain of algebraic-Fock endomorphisms with summable free Gibbs numerator. -/
noncomputable def freeGibbsDomain (ε : Mode → ℝ) (β : ℝ) :
    Submodule ℂ (FockSpace Mode →ₗ[ℂ] FockSpace Mode) where
  carrier := {A | freeGibbsSummable ε β A}
  zero_mem' := by
    change freeGibbsSummable ε β
      (0 : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    unfold freeGibbsSummable
    simpa [LinearMap.comp_zero, Common.matrixCoeff] using
      (summable_zero : Summable (fun _ : Occupation Mode => (0 : ℂ)))
  add_mem' := by
    intro A B hA hB
    change freeGibbsSummable ε β (A + B)
    unfold freeGibbsSummable at hA hB ⊢
    have h := hA.add hB
    simpa only [LinearMap.comp_add, Common.matrixCoeff_add] using h
  smul_mem' := by
    intro c A hA
    change freeGibbsSummable ε β (c • A)
    unfold freeGibbsSummable at hA ⊢
    have h := hA.mul_left c
    simpa only [LinearMap.comp_smul, Common.matrixCoeff_smul] using h

/-- The unnormalized free bosonic partition series, expressed as a summability-aware diagonal trace.
-/
noncomputable def freeGibbsPartition (ε : Mode → ℝ) (β : ℝ) : ℂ :=
  Common.tsumTrace (imaginaryTimeEvolveFree ε (-β))

/-- The normalized free bosonic Gibbs expectation whenever its numerator is summable and the
partition series is nonzero.  Positivity hypotheses proving the latter are supplied by subsequent
theorems rather than hidden in the definition. -/
noncomputable def freeGibbsExpectation (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) : ℂ :=
  Common.tsumTrace ((imaginaryTimeEvolveFree ε (-β)).comp A) /
    freeGibbsPartition ε β

omit [Fintype Mode] in
/-- The normalized free Gibbs expectation is additive on its explicit summability domain. -/
theorem freeGibbsExpectation_add (ε : Mode → ℝ) (β : ℝ)
    {A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode}
    (hA : freeGibbsSummable ε β A) (hB : freeGibbsSummable ε β B) :
    freeGibbsExpectation ε β (A + B) =
      freeGibbsExpectation ε β A + freeGibbsExpectation ε β B := by
  unfold freeGibbsExpectation
  rw [LinearMap.comp_add, Common.tsumTrace_add hA hB, add_div]

omit [Fintype Mode] in
/-- The normalized free Gibbs expectation is homogeneous on algebraic-Fock endomorphisms. -/
theorem freeGibbsExpectation_smul (ε : Mode → ℝ) (β : ℝ) (c : ℂ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (c • A) = c * freeGibbsExpectation ε β A := by
  unfold freeGibbsExpectation
  rw [LinearMap.comp_smul, Common.tsumTrace_smul, mul_div_assoc]

/-- The free Gibbs expectation as a linear map on the summable-operator submodule. -/
noncomputable def freeGibbsExpectationLinear (ε : Mode → ℝ) (β : ℝ) :
    freeGibbsDomain ε β →ₗ[ℂ] ℂ where
  toFun := fun A => freeGibbsExpectation ε β A.1
  map_add' := by
    intro A B
    exact freeGibbsExpectation_add ε β A.2 B.2
  map_smul' := by
    intro c A
    exact freeGibbsExpectation_smul ε β c A.1

/-- Under positive one-mode Boltzmann exponents, the free diagonal trace equals the convergent real
Boltzmann partition sum embedded in `ℂ`. -/
theorem freeGibbsPartition_eq_tsum (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    freeGibbsPartition ε β =
      ((∑' n : Occupation Mode, boltzmannWeight ε β n : ℝ) : ℂ) := by
  unfold freeGibbsPartition Common.tsumTrace
  have h := (hasSum_boltzmannWeight ε β hpos).mapL Complex.ofRealCLM
  have hpoint :
      (fun n : Occupation Mode => Complex.ofRealCLM (boltzmannWeight ε β n)) =
        fun n : Occupation Mode =>
          Common.matrixCoeff (imaginaryTimeEvolveFree ε (-β)) n n := by
    funext n
    rw [matrixCoeff_imaginaryTimeEvolveFree_self]
    simp [Complex.ofRealCLM_apply, boltzmannWeight]
  rw [hpoint] at h
  rw [tsum_boltzmannWeight ε β hpos]
  simpa [Complex.ofRealCLM_apply] using h.tsum_eq

/-- The free bosonic partition series is nonzero under the explicit positive-energy/temperature
hypothesis. -/
theorem freeGibbsPartition_ne_zero (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) : freeGibbsPartition ε β ≠ 0 := by
  rw [freeGibbsPartition_eq_tsum ε β hpos]
  exact Complex.ofReal_ne_zero.2 (tsum_boltzmannWeight_ne_zero ε β hpos)

/-- The identity endomorphism belongs to the free Gibbs summability domain. -/
theorem linearMap_id_mem_freeGibbsDomain (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) ∈ freeGibbsDomain ε β := by
  change freeGibbsSummable ε β
    (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
  unfold freeGibbsSummable
  rw [LinearMap.comp_id]
  exact summable_imaginaryTimeEvolveFree_self ε β hpos

/-- The free bosonic Gibbs expectation is normalized on the identity endomorphism. -/
theorem freeGibbsExpectation_id (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    freeGibbsExpectation ε β
      (LinearMap.id : FockSpace Mode →ₗ[ℂ] FockSpace Mode) = 1 := by
  rw [freeGibbsExpectation, LinearMap.comp_id]
  change freeGibbsPartition ε β / freeGibbsPartition ε β = 1
  exact div_self (freeGibbsPartition_ne_zero ε β hpos)

/-- The canonical convergence-aware free-boson Gibbs functional on algebraic Fock space. -/
noncomputable def freeGibbsFunctional (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) :
    ConvergenceAwareGibbsFunctional (FockSpace Mode →ₗ[ℂ] FockSpace Mode) where
  domain := freeGibbsDomain ε β
  expectation := freeGibbsExpectationLinear ε β
  unit := LinearMap.id
  unit_mem := linearMap_id_mem_freeGibbsDomain ε β hpos
  expectation_unit := freeGibbsExpectation_id ε β hpos

end
end Bosonic
end SecondQuantization
