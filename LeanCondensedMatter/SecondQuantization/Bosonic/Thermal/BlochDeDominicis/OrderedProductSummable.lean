import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.PolynomialOccupationWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.FreeThermalField
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-Gibbs summability of arbitrary fixed-length free thermal products

A finite ordered product of bosonic creation and annihilation operators sends every occupation-basis
state either to zero or to one occupation-basis state multiplied by a product of square-root ladder
factors. During a list of length `L`, no mode occupation can rise by more than `L`.

We dominate every ladder factor by a finite-mode product of shifted occupations. The shifted
polynomial Gibbs moments proved in `PolynomialOccupationWeightSummable` then make the diagonal Gibbs
numerator summable for every fixed finite list. This discharges the product-domain part of the
multi-point free-boson Wick/KMS boundary without any finite occupation-basis assumption.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- File-local classical decidable equality for finite-mode products. -/
local instance instDecidableEqOrderedProductSummable : DecidableEq Mode := Classical.decEq Mode

/-- A uniform product majorant for ladder factors after at most `K` field operations. -/
private noncomputable def orderedProductMajorant (n : Occupation Mode) (K : ℕ) : ℝ :=
  ∏ i, ((n i + K + 1 : ℕ) : ℝ)

/-- Every individual shifted occupation factor is bounded by the full finite-mode product majorant. -/
private theorem shiftedOccupation_le_orderedProductMajorant
    (n : Occupation Mode) (K : ℕ) (i : Mode) :
    ((n i + K + 1 : ℕ) : ℝ) ≤ orderedProductMajorant n K := by
  rw [orderedProductMajorant,
    ← Finset.mul_prod_erase Finset.univ
      (fun j => ((n j + K + 1 : ℕ) : ℝ)) (Finset.mem_univ i)]
  have hfactor : 0 ≤ ((n i + K + 1 : ℕ) : ℝ) := by positivity
  have hrest : 1 ≤ ∏ j ∈ Finset.univ.erase i, ((n j + K + 1 : ℕ) : ℝ) := by
    apply Finset.one_le_prod₀
    intro j hj
    exact_mod_cast (show 1 ≤ n j + K + 1 by omega)
  nlinarith

/-- The product majorant is nonnegative. -/
private theorem orderedProductMajorant_nonneg (n : Occupation Mode) (K : ℕ) :
    0 ≤ orderedProductMajorant n K := by
  rw [orderedProductMajorant]
  exact Finset.prod_nonneg fun i _ => by positivity

/-- A single ladder factor is bounded by the same polynomial majorant for either ladder kind. -/
private theorem sqrt_natCast_le_orderedProductMajorant
    (n : Occupation Mode) (K k : ℕ) (i : Mode)
    (hk : k ≤ n i + K + 1) :
    Real.sqrt (k : ℝ) ≤ orderedProductMajorant n K := by
  have hle : (k : ℝ) ≤ ((n i + K + 1 : ℕ) : ℝ) := by
    exact_mod_cast hk
  have hs := Real.sqrt_le_sqrt hle
  have hR0 : 0 ≤ ((n i + K + 1 : ℕ) : ℝ) := by positivity
  have hsRsq := Real.sq_sqrt hR0
  have hR1 : 1 ≤ ((n i + K + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n i + K + 1 by omega)
  have hsR : Real.sqrt (((n i + K + 1 : ℕ) : ℝ)) ≤
      ((n i + K + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sqrt_nonneg (((n i + K + 1 : ℕ) : ℝ))]
  exact (hs.trans hsR).trans (shiftedOccupation_le_orderedProductMajorant n K i)

/-- Multiplying a bounded coefficient by one bounded nonnegative ladder factor adds one power. -/
private theorem norm_mul_real_le_pow_succ
    (B : ℝ) (hB : 0 ≤ B) (c : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (haB : a ≤ B) (k : ℕ) (hc : ‖c‖ ≤ B ^ k) :
    ‖c * (a : ℂ)‖ ≤ B ^ (k + 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, pow_succ]
  exact mul_le_mul hc haB ha (pow_nonneg hB _)

/-- Basis-state action of an arbitrary free-thermal-field list, with a uniform coefficient bound.

`K` is an external upper bound on the list length. Keeping it fixed through the induction avoids
changing the majorant while fields are peeled from the left. -/
private theorem FreeThermalField.orderedProduct_basisState_bound_aux
    (fields : List (FreeThermalField Mode)) (n : Occupation Mode) (K : ℕ)
    (hK : fields.length ≤ K) :
    ∃ c : ℂ, ∃ m : Occupation Mode,
      FreeThermalField.orderedProduct fields (basisState n) = c • basisState m ∧
      (∀ i, m i ≤ n i + fields.length) ∧
      ‖c‖ ≤ (orderedProductMajorant n K) ^ fields.length := by
  induction fields with
  | nil =>
      refine ⟨1, n, ?_, ?_, ?_⟩
      · simp [FreeThermalField.orderedProduct]
      · intro i
        simp
      · simp
  | cons field fields ih =>
      have hKtail : fields.length ≤ K := by
        simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ fields.length) hK
      rcases ih hKtail with ⟨c, m, haction, hm, hc⟩
      have hB0 := orderedProductMajorant_nonneg n K
      cases field with
      | create i =>
          let a : ℝ := Real.sqrt (m i + 1 : ℝ)
          refine ⟨c * (a : ℂ), createOccupation i m, ?_, ?_, ?_⟩
          · simp only [FreeThermalField.orderedProduct_cons, LinearMap.comp_apply,
              FreeThermalField.operator]
            rw [haction, map_smul, create_basisState_eq, smul_smul]
          · intro j
            simp only [List.length_cons]
            by_cases hji : j = i
            · subst j
              rw [createOccupation_apply_same]
              have hmi := hm i
              omega
            · rw [createOccupation_apply_ne hji]
              have hmj := hm j
              omega
          · have hmK : m i + 1 ≤ n i + K + 1 := by
              have hmi := hm i
              omega
            have haB : a ≤ orderedProductMajorant n K := by
              simpa only [a, Nat.cast_add, Nat.cast_one] using
                (sqrt_natCast_le_orderedProductMajorant n K (m i + 1) i hmK)
            exact norm_mul_real_le_pow_succ (orderedProductMajorant n K) hB0
              c a (Real.sqrt_nonneg _) haB fields.length hc
      | annihilate i =>
          by_cases hi : m i = 0
          · refine ⟨0, m, ?_, ?_, ?_⟩
            · simp only [FreeThermalField.orderedProduct_cons, LinearMap.comp_apply, FreeThermalField.operator]
              rw [haction, map_smul, annihilate_basisState_of_zero hi, smul_zero]
              simp
            · intro j
              have hmj := hm j
              simp only [List.length_cons]
              omega
            · simp only [norm_zero]
              exact pow_nonneg hB0 _
          · let a : ℝ := Real.sqrt (m i : ℝ)
            refine ⟨c * (a : ℂ), removeOccupation i m, ?_, ?_, ?_⟩
            · simp only [FreeThermalField.orderedProduct_cons, LinearMap.comp_apply, FreeThermalField.operator]
              rw [haction, map_smul, annihilate_basisState_of_pos hi, smul_smul]
            · intro j
              simp only [List.length_cons]
              by_cases hji : j = i
              · subst j
                rw [removeOccupation_apply_same]
                have hmi := hm i
                omega
              · rw [removeOccupation_apply_ne hji]
                have hmj := hm j
                omega
            · have hmK : m i ≤ n i + K + 1 := by
                have hmi := hm i
                omega
              have haB : a ≤ orderedProductMajorant n K :=
                sqrt_natCast_le_orderedProductMajorant n K (m i) i hmK
              exact norm_mul_real_le_pow_succ (orderedProductMajorant n K) hB0
                c a (Real.sqrt_nonneg _) haB fields.length hc

/-- Diagonal matrix coefficients of an arbitrary fixed free-thermal-field list have polynomial
growth controlled by a uniform finite-mode product. -/
theorem FreeThermalField.norm_matrixCoeff_orderedProduct_le
    (fields : List (FreeThermalField Mode)) (n : Occupation Mode) :
    ‖Common.matrixCoeff (FreeThermalField.orderedProduct fields) n n‖ ≤
      (orderedProductMajorant n fields.length) ^ fields.length := by
  rcases FreeThermalField.orderedProduct_basisState_bound_aux
      fields n fields.length (le_refl _) with ⟨c, m, haction, _, hc⟩
  rw [Common.matrixCoeff_eq_ite_of_basisState_smul haction]
  split_ifs
  · simpa using hc
  · rw [norm_zero]
    exact pow_nonneg (orderedProductMajorant_nonneg n fields.length) _

/-- Every finite ordered product of free bosonic thermal fields has a summable
grand-canonical Gibbs numerator under positive effective one-mode Boltzmann exponents. -/
theorem FreeThermalField.orderedProduct_mem_grandCanonicalGibbsDomain
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (fields : List (FreeThermalField Mode)) :
    FreeThermalField.orderedProduct fields ∈ grandCanonicalGibbsDomain ε β μ := by
  let ξ : Mode → ℝ := fun i => ε i - μ
  change Summable (fun n : Occupation Mode =>
    Common.matrixCoeff ((imaginaryTimeEvolveFree ξ (-β)).comp
      (FreeThermalField.orderedProduct fields)) n n)
  have hmajorant := summable_shiftedOccupationPowerProduct_boltzmannWeight
    ξ β hpos (fun _ => fields.length + 1) (fun _ => fields.length)
  apply hmajorant.of_norm_bounded
  intro n
  rw [show imaginaryTimeEvolveFree ξ (-β) =
      Common.diagonalEvolution (freeEigenvalue ξ) (-β) by rfl,
    Common.matrixCoeff_diagonalEvolution_comp, norm_mul, Complex.norm_exp]
  change boltzmannWeight ξ β n *
      ‖Common.matrixCoeff (FreeThermalField.orderedProduct fields) n n‖ ≤ _
  have hcoeff := FreeThermalField.norm_matrixCoeff_orderedProduct_le fields n
  have heq :
      (orderedProductMajorant n fields.length) ^ fields.length =
        ∏ i, ((n i + (fields.length + 1) : ℕ) : ℝ) ^ fields.length := by
    rw [orderedProductMajorant]
    calc
      (∏ i, ((n i + fields.length + 1 : ℕ) : ℝ)) ^ fields.length =
          (∏ i, ((n i + (fields.length + 1) : ℕ) : ℝ)) ^ fields.length := by
        congr 1
      _ = ∏ i, ((n i + (fields.length + 1) : ℕ) : ℝ) ^ fields.length := by
        rw [Finset.prod_pow]
  rw [heq] at hcoeff
  calc
    boltzmannWeight ξ β n *
        ‖Common.matrixCoeff (FreeThermalField.orderedProduct fields) n n‖ ≤
      boltzmannWeight ξ β n *
        (∏ i, ((n i + (fields.length + 1) : ℕ) : ℝ) ^ fields.length) :=
      mul_le_mul_of_nonneg_left hcoeff (Real.exp_nonneg _)
    _ = (∏ i, ((n i + (fields.length + 1) : ℕ) : ℝ) ^ fields.length) *
        boltzmannWeight ξ β n := by ring

end
end Bosonic
end SecondQuantization
