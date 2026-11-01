import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.FiniteTable
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertSelfAdjoint
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.FrequencyDomain
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

set_option linter.style.header false

/-! # Full-Fock Lehmann response of two fermionic modes

The current vertices are creation-annihilation bilinears on all four occupation states.
The only off-diagonal transitions are between the two singleton occupations; vacuum and
double occupation do not contribute to the commutator response. The probabilities below
are many-body probabilities, not normalized one-particle occupations.
-/

namespace SecondQuantization.Fermionic.Transport

open QuantumTheory.LinearResponse
open scoped BigOperators

noncomputable section

private def twoModeVertex (A : Matrix (Fin 2) (Fin 2) ℂ) :
    OccupationFock (Fin 2) →ₗ[ℂ] OccupationFock (Fin 2) :=
  ∑ i, ∑ j, A i j • (create i).comp (annihilate j)

/-- The full four-state Fock spectral table of two independent modes and one-body vertices.
Physical diagonal states supply nonnegative probabilities whose sum is one. -/
private def twoModeFockLehmannTable (energy : Fin 2 → ℝ)
    (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    FiniteLehmannTable (Occupation (Fin 2)) where
  energy := fermionEnergy energy
  probability := probability
  matrixA := Common.matrixCoeff (twoModeVertex A)
  matrixB := Common.matrixCoeff (twoModeVertex B)

/-- Bounded full-Fock dynamics of the two independent energy modes. -/
private def twoModeFockSystem (energy : Fin 2 → ℝ) (hbar : ℝ) (hhbar : 0 < hbar) :
    BoundedFreeSystem (Common.FiniteHilbertFock (Occupation (Fin 2))) where
  hamiltonian := ⟨Common.finiteHilbertOperatorAlgEquiv (freeHamiltonian energy), by
    rw [isSelfAdjoint_iff, Common.star_finiteHilbertOperator_eq_iff_matrixCoeff]
    intro m n
    by_cases h : m = n
    · subst n
      simp [freeHamiltonian, Common.matrixCoeff_diagonalOperator]
    · simp [freeHamiltonian, Common.matrixCoeff_diagonalOperator, h, Ne.symm h]⟩
  hbar := hbar
  hbar_pos := hhbar

/-- A normalized diagonal probability on all four Fock states supplies the actual state data
of the Kubo theorem, without replacing those probabilities by one-particle occupations. -/
private def twoModeFockEigenbasisData (energy : Fin 2 → ℝ)
    (probability : Occupation (Fin 2) → ℝ) (hbar : ℝ) (hhbar : 0 < hbar)
    (hpos : ∀ n, 0 ≤ probability n) (hsum : HasSum probability 1) :
    EnergyEigenbasisLehmannData (twoModeFockSystem energy hbar hhbar) (Occupation (Fin 2)) where
  basis := Common.finiteHilbertBasis
  energy := fermionEnergy energy
  probability := probability
  probability_nonneg := hpos
  probability_hasSum := hsum
  hamiltonian_apply_basis := by
    intro n
    change Common.finiteHilbertOperatorAlgEquiv (freeHamiltonian energy)
      (Common.finiteHilbertBasis n) = _
    rw [Common.finiteHilbertBasis_apply, Common.finiteHilbertOperator_basisState]
    have h := freeHamiltonian_basisState energy n
    change freeHamiltonian energy (Common.basisState n) = _ at h
    rw [h, map_smul]
    simp only [basisState, Common.finiteHilbertFockEquiv_basisState]

/-- The four-state scalar response is supplied by the existing operator-level causal Kubo
theorem for the bounded creation-annihilation vertices and the normalized diagonal state. -/
private theorem twoModeFockLehmannTableResponse_eq_kubo
    (energy : Fin 2 → ℝ) (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hbar omega eta : ℝ) (hhbar : 0 < hbar)
    (hpos : ∀ n, 0 ≤ probability n) (hsum : HasSum probability 1) (heta : 0 < eta) :
    let S := twoModeFockSystem energy hbar hhbar
    let D := twoModeFockEigenbasisData energy probability hbar hhbar hpos hsum
    finiteLehmannTableResponse hbar omega eta (twoModeFockLehmannTable energy probability A B) =
      adiabaticFrequencyDomainSusceptibility (freePropagatorGroup S) hbar
        (eigenbasisNormalizedExpectation S D)
        (Common.finiteHilbertOperatorAlgEquiv (twoModeVertex A))
        (Common.finiteHilbertOperatorAlgEquiv (twoModeVertex B)) omega eta := by
  dsimp only
  have hcoeff (V : OccupationFock (Fin 2) →ₗ[ℂ] OccupationFock (Fin 2))
      (m n : Occupation (Fin 2)) :
      inner ℂ (Common.finiteHilbertBasis m)
        (Common.finiteHilbertOperatorAlgEquiv V (Common.finiteHilbertBasis n)) =
          Common.matrixCoeff V m n := by
    simp only [Common.finiteHilbertBasis_apply, Common.finiteHilbertBasisState,
      EuclideanSpace.basisFun_apply]
    rw [EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    simpa only [Common.finiteHilbertBasisState, EuclideanSpace.basisFun_apply] using
      Common.finiteHilbertOperator_basis_apply V m n
  calc
    _ = ∑ mn : Occupation (Fin 2) × Occupation (Fin 2),
        (eigenbasisTransitionData (twoModeFockSystem energy hbar hhbar)
          (twoModeFockEigenbasisData energy probability hbar hhbar hpos hsum)
          (Common.finiteHilbertOperatorAlgEquiv (twoModeVertex A))
          (Common.finiteHilbertOperatorAlgEquiv (twoModeVertex B)) mn).frequencyTerm omega eta := by
      simp only [finiteLehmannTableResponse, finiteLehmannTableTransitionData,
        twoModeFockLehmannTable, eigenbasisTransitionData, twoModeFockEigenbasisData, hcoeff,
        twoModeFockSystem]
    _ = _ := (adiabaticFrequencyDomainSusceptibility_eigenbasis_eq_finite_sum
      (twoModeFockSystem energy hbar hhbar)
      (twoModeFockEigenbasisData energy probability hbar hhbar hpos hsum)
      (Common.finiteHilbertOperatorAlgEquiv (twoModeVertex A))
      (Common.finiteHilbertOperatorAlgEquiv (twoModeVertex B)) omega eta heta).symm

set_option maxHeartbeats 800000 in
-- Expanding the four occupation states evaluates the creation-annihilation signs explicitly.
/-- Summing all many-body transitions leaves exactly the two one-particle transfer terms.
No normalization or thermal assumption is needed for this algebraic reduction. -/
private theorem twoModeFockLehmannTableResponse_eq
    (energy : Fin 2 → ℝ) (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hbar omega eta : ℝ) :
    finiteLehmannTableResponse hbar omega eta
        (twoModeFockLehmannTable energy probability A B) =
      (orderedLehmannTransitionData hbar (energy 0) (energy 1)
        (probability {0}) (probability {1}) (A 0 1) (B 1 0)).frequencyTerm omega eta +
      (orderedLehmannTransitionData hbar (energy 1) (energy 0)
        (probability {1}) (probability {0}) (A 1 0) (B 0 1)).frequencyTerm omega eta := by
  classical
  have hstates : (Finset.univ : Finset (Occupation (Fin 2))) =
      {∅, {0}, {1}, {0, 1}} := by decide
  have hsum (f : Occupation (Fin 2) → ℂ) :
      (∑ n, f n) = f ∅ + f {0} + f {1} + f {0, 1} := by
    rw [hstates]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have ha (i : Fin 2) (n : Occupation (Fin 2)) :
      annihilate i (Common.basisState n) =
        if i ∈ n then (fermionSign i n : ℂ) • Common.basisState (removeOccupation i n) else 0 := by
    simpa only [basisState, annihilateBasis] using annihilate_basisState i n
  have hc (i : Fin 2) (n : Occupation (Fin 2)) :
      create i (Common.basisState n) =
        if i ∈ n then 0 else (fermionSign i n : ℂ) • Common.basisState (insertOccupation i n) := by
    simpa only [basisState, createBasis] using create_basisState i n
  have hf : ({1} : Occupation (Fin 2)).filter (fun i => i = 0) = ∅ := by decide
  have hn : ({0} : Occupation (Fin 2)) ≠ {0, 1} := by decide
  unfold finiteLehmannTableResponse
  rw [Fintype.sum_prod_type]
  simp_rw [hsum]
  simp only [twoModeFockLehmannTable, finiteLehmannTableTransitionData,
    LehmannTransitionData.frequencyTerm, orderedLehmannTransitionData,
    lehmannTerm, twoModeVertex, Common.matrixCoeff,
    Fin.sum_univ_two, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]
  simp [ha, hc,
    map_smul, fermionSign, insertOccupation, removeOccupation,
    fermionEnergy_eq_sum]
  simp [Common.basisState, hf, hn, Ne.symm hn]

/-- Antisymmetric current response converted from vector potential to electric field at zero
frequency. This is a response density before a momentum measure or volume factor is applied. -/
private def twoModeFockHallResponse (energy : Fin 2 → ℝ)
    (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hbar eta : ℝ) : ℂ :=
  (finiteLehmannTableResponse hbar 0 eta (twoModeFockLehmannTable energy probability A B) -
    finiteLehmannTableResponse hbar 0 eta (twoModeFockLehmannTable energy probability B A)) /
      (2 * (-(eta : ℂ)))

/-- Real clean Hall coefficient obtained from the full Fock response. The imaginary part is
the antisymmetric spectral current numerator, not a real-valued conversion of an operator. -/
def twoModeFockHallCleanResponse (energy : Fin 2 → ℝ)
    (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hbar : ℝ) : ℝ :=
  hbar * (probability {0} - probability {1}) *
    (A 0 1 * B 1 0 - B 0 1 * A 1 0).im / (energy 0 - energy 1) ^ 2

/-- The clean Hall coefficient is the actual positive-switching-rate limit of the four-state
Fock Lehmann response, including the electric-field conversion. -/
private theorem tendsto_twoModeFockHallResponse_re
    (energy : Fin 2 → ℝ) (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hbar : ℝ) (hhbar : hbar ≠ 0)
    (hgap : energy 0 - energy 1 ≠ 0) :
    Filter.Tendsto (fun eta : ℝ => (twoModeFockHallResponse energy probability A B hbar eta).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoModeFockHallCleanResponse energy probability A B hbar)) := by
  let gap := energy 0 - energy 1
  let numerator := -Complex.I / (hbar : ℂ) *
    ((probability {0} - probability {1} : ℝ) : ℂ) *
      (A 0 1 * B 1 0 - B 0 1 * A 1 0)
  let F := fun eta : ℝ => numerator /
    (lehmannDenominator hbar 0 eta gap * lehmannDenominator hbar 0 eta (-gap))
  have hhbarC : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar
  have hrewrite (eta : ℝ) (heta : 0 < eta) :
      twoModeFockHallResponse energy probability A B hbar eta = F eta := by
    have hden := lehmannDenominator_ne_zero hbar 0 eta gap heta.ne'
    have hden' := lehmannDenominator_ne_zero hbar 0 eta (-gap) heta.ne'
    have hetaC : (eta : ℂ) ≠ 0 := by exact_mod_cast heta.ne'
    unfold twoModeFockHallResponse
    rw [twoModeFockLehmannTableResponse_eq, twoModeFockLehmannTableResponse_eq]
    have hswap : energy 1 - energy 0 = -gap := by dsimp [gap]; ring
    have hforward : energy 0 - energy 1 = gap := rfl
    simp only [LehmannTransitionData.frequencyTerm, orderedLehmannTransitionData,
      lehmannTerm, hswap, hforward]
    change _ = numerator /
      (lehmannDenominator hbar 0 eta gap * lehmannDenominator hbar 0 eta (-gap))
    dsimp [numerator]
    field_simp [hden, hden', hetaC, hhbarC]
    simp only [lehmannDenominator]
    push_cast
    ring
  have hgapC : (gap : ℂ) ≠ 0 := by exact_mod_cast hgap
  have hden0 : lehmannDenominator hbar 0 0 gap *
      lehmannDenominator hbar 0 0 (-gap) ≠ 0 := by
    simp [lehmannDenominator, hgapC, hhbarC]
  have hcont : ContinuousAt F 0 := by
    apply ContinuousAt.div continuousAt_const
    · dsimp [lehmannDenominator]
      fun_prop
    · exact hden0
  have heval : F 0 =
      -(Complex.I * (hbar : ℂ)) * ((probability {0} - probability {1} : ℝ) : ℂ) *
        (A 0 1 * B 1 0 - B 0 1 * A 1 0) / (gap : ℂ) ^ 2 := by
    dsimp [F, numerator, lehmannDenominator]
    push_cast
    field_simp [hhbarC, hgapC]
    ring_nf; norm_num; ring
  have hreal : (F 0).re = twoModeFockHallCleanResponse energy probability A B hbar := by
    rw [heval]
    rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, one_mul, zero_add,
      twoModeFockHallCleanResponse]
    dsimp only [gap]
    ring
  have hlimit : Filter.Tendsto (fun eta => (F eta).re) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (F 0).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  rw [hreal] at hlimit
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact congrArg Complex.re (hrewrite eta heta).symm

/-- Antisymmetric physical Kubo susceptibility in the normalized full-Fock state, including
the zero-frequency vector-potential to electric-field factor. -/
def twoModeFockHallKuboResponse (energy : Fin 2 → ℝ)
    (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hbar : ℝ) (hhbar : 0 < hbar)
    (hpos : ∀ n, 0 ≤ probability n) (hsum : HasSum probability 1) (eta : ℝ) : ℂ :=
  let S := twoModeFockSystem energy hbar hhbar
  let D := twoModeFockEigenbasisData energy probability hbar hhbar hpos hsum
  let omega := eigenbasisNormalizedExpectation S D
  let VA := Common.finiteHilbertOperatorAlgEquiv (twoModeVertex A)
  let VB := Common.finiteHilbertOperatorAlgEquiv (twoModeVertex B)
  (adiabaticFrequencyDomainSusceptibility (freePropagatorGroup S) hbar omega VA VB 0 eta -
    adiabaticFrequencyDomainSusceptibility (freePropagatorGroup S) hbar omega VB VA 0 eta) /
      (2 * (-(eta : ℂ)))

/-- The clean density follows from the actual full-Fock Kubo theory for every normalized
diagonal state. The hypotheses concern the chosen state and the one-particle gap only. -/
theorem tendsto_twoModeFockHallKuboResponse_re
    (energy : Fin 2 → ℝ) (probability : Occupation (Fin 2) → ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hbar : ℝ) (hhbar : 0 < hbar)
    (hpos : ∀ n, 0 ≤ probability n) (hsum : HasSum probability 1)
    (hgap : energy 0 - energy 1 ≠ 0) :
    Filter.Tendsto (fun eta =>
      (twoModeFockHallKuboResponse energy probability A B hbar hhbar hpos hsum eta).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (twoModeFockHallCleanResponse energy probability A B hbar)) := by
  have h := tendsto_twoModeFockHallResponse_re energy probability A B hbar hhbar.ne' hgap
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  congr 1
  unfold twoModeFockHallResponse twoModeFockHallKuboResponse
  rw [twoModeFockLehmannTableResponse_eq_kubo energy probability A B hbar 0 eta hhbar hpos hsum heta,
    twoModeFockLehmannTableResponse_eq_kubo energy probability B A hbar 0 eta hhbar hpos hsum heta]

end
end SecondQuantization.Fermionic.Transport
