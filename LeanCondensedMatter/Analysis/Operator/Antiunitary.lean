import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Star

set_option linter.style.header false

/-!
# Antiunitary maps and operator conjugation

An antiunitary is a continuous conjugate-linear equivalence of Hilbert-space
vectors that conjugates the complex inner product. Additivity, semilinearity,
bijectivity, continuity and the inverse map are inherited from Mathlib rather
than repeated as independent structure fields.

The induced conjugation on bounded operators preserves multiplication and exponentiation,
is conjugate-linear, and conjugates the ordinary finite-dimensional trace.
-/

/-- A continuous conjugate-linear equivalence conjugating the Hilbert-space
inner product. No condition on its square is imposed, so Kramers time reversal
with square minus identity is permitted. -/
structure AntiunitaryMap (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The bijective continuous conjugate-linear action on state vectors. -/
  equiv : H ≃L⋆[ℂ] H
  /-- Antiunitarity: inner products are complex conjugated. -/
  inner_map : ∀ x y,
    inner ℂ (equiv x) (equiv y) = (starRingEnd ℂ) (inner ℂ x y)

noncomputable section

namespace AntiunitaryMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (Θ : AntiunitaryMap H)

/-- Conjugation of a bounded operator by a state-space antiunitary.
Boundedness does not require the space to be finite dimensional. -/
noncomputable def conjugateOperator (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (Θ.equiv.arrowCongrSL Θ.equiv) A

@[simp]
theorem conjugateOperator_apply (A : H →L[ℂ] H) (x : H) :
    Θ.conjugateOperator A x = Θ.equiv (A (Θ.equiv.symm x)) := rfl

@[simp]
theorem conjugateOperator_mul (A B : H →L[ℂ] H) :
    Θ.conjugateOperator (A * B) =
      Θ.conjugateOperator A * Θ.conjugateOperator B := by
  ext x
  simp [conjugateOperator_apply]

@[simp]
theorem conjugateOperator_smul (c : ℂ) (A : H →L[ℂ] H) :
    Θ.conjugateOperator (c • A) =
      ((starRingEnd ℂ) c) • Θ.conjugateOperator A :=
  (Θ.equiv.arrowCongrSL Θ.equiv).map_smulₛₗ c A

/-- Antiunitary conjugation commutes with bounded-operator exponentiation
on any complete complex inner-product space. -/
theorem conjugateOperator_exp [CompleteSpace H]
    (A : H →L[ℂ] H) :
    Θ.conjugateOperator (NormedSpace.exp A) =
      NormedSpace.exp (Θ.conjugateOperator A) := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let f : (H →L[ℂ] H) →+* (H →L[ℂ] H) :=
    { (Θ.equiv.arrowCongrSL Θ.equiv).toLinearEquiv.toAddEquiv.toAddMonoidHom with
      map_one' := by ext x; exact Θ.equiv.apply_symm_apply x
      map_mul' := Θ.conjugateOperator_mul }
  exact NormedSpace.map_exp f (Θ.equiv.arrowCongrSL Θ.equiv).continuous A

end AntiunitaryMap

end

open ContinuousLinearMap

noncomputable section

namespace AntiunitaryMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]
variable (Θ : AntiunitaryMap H)

/-- The ordinary finite-dimensional trace is conjugated by the induced
operator action of any antiunitary on the Hilbert space. -/
theorem conjugateOperator_trace (A : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (Θ.conjugateOperator A) =
      star (finiteDimensionalOperatorTrace A) := by
  classical
  let b := stdOrthonormalBasis ℂ H
  have horth : Orthonormal ℂ (fun i => Θ.equiv (b i)) := by
    apply (orthonormal_iff_ite).2
    intro i j
    rw [Θ.inner_map, (orthonormal_iff_ite).1 b.orthonormal i j]
    split_ifs <;> simp
  have horth' :
      Orthonormal ℂ
        ((Set.univ : Set (Fin (Module.finrank ℂ H))).domRestrict
          (fun i => Θ.equiv (b i))) := by
    change Orthonormal ℂ
      (fun i : (Set.univ : Set (Fin (Module.finrank ℂ H))) => Θ.equiv (b i))
    exact horth.comp
      (fun i : (Set.univ : Set (Fin (Module.finrank ℂ H))) => (i : Fin (Module.finrank ℂ H)))
      Subtype.val_injective
  obtain ⟨b', hb'⟩ :=
    horth'.exists_orthonormalBasis_extension_of_card_eq
      (Module.finrank_eq_card_basis b.toBasis)
  have hb' (i) : b' i = Θ.equiv (b i) := hb' i (Set.mem_univ i)
  rw [finiteDimensionalOperatorTrace_apply, finiteDimensionalOperatorTrace_apply,
    LinearMap.trace_eq_sum_inner _ b', LinearMap.trace_eq_sum_inner _ b, star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb' i]
  change inner ℂ (Θ.equiv (b i))
      (Θ.equiv (A (Θ.equiv.symm (Θ.equiv (b i))))) =
    (starRingEnd ℂ) (inner ℂ (b i) (A (b i)))
  rw [Θ.equiv.symm_apply_apply]
  exact Θ.inner_map (b i) (A (b i))

end AntiunitaryMap

end
