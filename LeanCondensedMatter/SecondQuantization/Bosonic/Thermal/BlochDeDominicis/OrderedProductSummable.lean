import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.PolynomialOccupationWeightSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalCompositionMatrixCoeff

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
    apply Finset.one_le_prod
    intro j hj
    exact_mod_cast (show 1 ≤ n j + K + 1 by omega)
  nlinarith

/-- The product majorant is nonnegative. -/
private theorem orderedProductMajorant_nonneg (n : Occupation Mode) (K : ℕ) :
    0 ≤ orderedProductMajorant n K := by
  rw [orderedProductMajorant]
  exact Finset.prod_nonneg fun i _ => by positivity

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
          · simp only [FreeThermalField.orderedProduct, LinearMap.comp_apply,
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
            have hsqrt : a ≤ ((n i + K + 1 : ℕ) : ℝ) := by
              have hle : (m i + 1 : ℝ) ≤ ((n i + K + 1 : ℕ) : ℝ) := by
                exact_mod_cast hmK
              have hs := Real.sqrt_le_sqrt hle
              have hR0 : 0 ≤ ((n i + K + 1 : ℕ) : ℝ) := by positivity
              have hsRsq := Real.sq_sqrt hR0
              have hR1 : 1 ≤ ((n i + K + 1 : ℕ) : ℝ) := by
                exact_mod_cast (show 1 ≤ n i + K + 1 by omega)
              have hsR : Real.sqrt (((n i + K + 1 : ℕ) : ℝ)) ≤
                  ((n i + K + 1 : ℕ) : ℝ) := by
                nlinarith [Real.sqrt_nonneg (((n i + K + 1 : ℕ) : ℝ))]
              exact hs.trans hsR
            have haB : a ≤ orderedProductMajorant n K :=
              hsqrt.trans (shiftedOccupation_le_orderedProductMajorant n K i)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
            calc
              ‖c‖ * a ≤ (orderedProductMajorant n K) ^ fields.length *
                  orderedProductMajorant n K :=
                mul_le_mul hc haB (Real.sqrt_nonneg _) (pow_nonneg hB0 _)
              _ = (orderedProductMajorant n K) ^
                    (FreeThermalField.create i :: fields).length := by
                simp only [List.length_cons, pow_succ]
      | annihilate i =>
          by_cases hi : m i = 0
          · refine ⟨0, m, ?_, ?_, ?_⟩
            · simp only [FreeThermalField.orderedProduct, LinearMap.comp_apply,
                FreeThermalField.operator]
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
            · simp only [FreeThermalField.orderedProduct, LinearMap.comp_apply,
                FreeThermalField.operator]
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
              have hsqrt : a ≤ ((n i + K + 1 : ℕ) : ℝ) := by
                have hle : (m i : ℝ) ≤ ((n i + K + 1 : ℕ) : ℝ) := by
                  exact_mod_cast hmK
                have hs := Real.sqrt_le_sqrt hle
                have hR0 : 0 ≤ ((n i + K + 1 : ℕ) : ℝ) := by positivity
                have hsRsq := Real.sq_sqrt hR0
                have hR1 : 1 ≤ ((n i + K + 1 : ℕ) : ℝ) := by
                  exact_mod_cast (show 1 ≤ n i + K + 1 by omega)
                have hsR : Real.sqrt (((n i + K + 1 : ℕ) : ℝ)) ≤
                    ((n i + K + 1 : ℕ) : ℝ) := by
                  nlinarith [Real.sqrt_nonneg (((n i + K + 1 : ℕ) : ℝ))]
                exact hs.trans hsR
              have haB : a ≤ orderedProductMajorant n K :=
                hsqrt.trans (shiftedOccupation_le_orderedProductMajorant n K i)
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _)]
              calc
                ‖c‖ * a ≤ (orderedProductMajorant n K) ^ fields.length *
                    orderedProductMajorant n K :=
                  mul_le_mul hc haB (Real.sqrt_nonneg _) (pow_nonneg hB0 _)
                _ = (orderedProductMajorant n K) ^
                      (FreeThermalField.annihilate i :: fields).length := by
                  simp only [List.length_cons, pow_succ]

/-- Diagonal matrix coefficients of an arbitrary fixed free-thermal-field list have polynomial
growth controlled by a uniform finite-mode product. -/
theorem FreeThermalField.norm_matrixCoeff_orderedProduct_le
    (fields : List (FreeThermalField Mode)) (n : Occupation Mode) :
    ‖Common.matrixCoeff (FreeThermalField.orderedProduct fields) n n‖ ≤
      (orderedProductMajorant n fields.length) ^ fields.length := by
  rcases FreeThermalField.orderedProduct_basisState_bound_aux
      fields n fields.length (le_refl _) with ⟨c, m, haction, _, hc⟩
  unfold Common.matrixCoeff
  change ‖(FreeThermalField.orderedProduct fields (basisState n)) n‖ ≤ _
  rw [haction]
  by_cases hmn : m = n
  · change ‖(c • Common.basisState m) n‖ ≤ _
    rw [hmn, Common.smul_basisState_apply_self]
    simpa using hc
  · change ‖(c • Common.basisState m) n‖ ≤ _
    rw [Common.smul_basisState_apply_of_ne c hmn, norm_zero]
    exact pow_nonneg (orderedProductMajorant_nonneg n fields.length) _

/-- Every finite ordered product of free bosonic thermal fields has a summable free-Gibbs numerator
under positive one-mode Boltzmann exponents. -/
theorem FreeThermalField.freeGibbsSummable_orderedProduct
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (fields : List (FreeThermalField Mode)) :
    freeGibbsSummable ε β (FreeThermalField.orderedProduct fields) := by
  unfold freeGibbsSummable
  have hmajorant := summable_shiftedOccupationPowerProduct_boltzmannWeight
    ε β hpos (fields.length + 1) fields.length
  apply hmajorant.of_norm_bounded
  intro n
  rw [show imaginaryTimeEvolveFree ε (-β) =
      Common.diagonalEvolution (freeEigenvalue ε) (-β) by rfl,
    Common.matrixCoeff_diagonalEvolution_comp, norm_mul, Complex.norm_exp]
  change boltzmannWeight ε β n *
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
    boltzmannWeight ε β n *
        ‖Common.matrixCoeff (FreeThermalField.orderedProduct fields) n n‖ ≤
      boltzmannWeight ε β n *
        (∏ i, ((n i + (fields.length + 1) : ℕ) : ℝ) ^ fields.length) :=
      mul_le_mul_of_nonneg_left hcoeff (Real.exp_nonneg _)
    _ = (∏ i, ((n i + (fields.length + 1) : ℕ) : ℝ) ^ fields.length) *
        boltzmannWeight ε β n := by ring

/-- Domain form of fixed-length free thermal ordered-product summability. -/
theorem FreeThermalField.orderedProduct_mem_freeGibbsDomain
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (fields : List (FreeThermalField Mode)) :
    FreeThermalField.orderedProduct fields ∈ freeGibbsDomain ε β :=
  FreeThermalField.freeGibbsSummable_orderedProduct ε β hpos fields

end
end Bosonic
end SecondQuantization
