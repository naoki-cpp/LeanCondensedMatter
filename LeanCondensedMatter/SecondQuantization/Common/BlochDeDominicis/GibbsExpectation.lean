import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.FourPointReduction
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelTermsIndexed
import LeanCondensedMatter.SecondQuantization.Common.NormalizedOperatorFunctional

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# The normalized Gibbs expectation, as a `boltzmannWeight`-specialized `normalizedWeightedDiagonal`

Every Bloch–de Dominicis theorem proved so far (`TwoPoint.lean`, `FourPointReduction.lean`,
`PeelFirst.lean`/`PeelFirstTrace.lean`) is stated in terms of the *un-normalized* `traceFock`/
`tsumTrace` of `e^{-βH₀}X`, deliberately left un-divided so callers choose whether/how to divide.
The genuine physical statement of the theorem — e.g. the 4-point expansion `⟨C₁C₂C₃C₄⟩_β =
⟨C₁C₂⟩_β⟨C₃C₄⟩_β + ζ⟨C₁C₃⟩_β⟨C₂C₄⟩_β + ⟨C₁C₄⟩_β⟨C₂C₃⟩_β` (for `ζ = ±1`, the project's physics
reference notes, `quantum-statistical-mechanics.tex`) — is a product of *normalized* 2-point
*numbers*, not un-normalized traces. This file introduces that normalized functional.

**Not a new abstraction — a `boltzmannWeight`-specialized instance of the existing
`Common.normalizedWeightedDiagonal`** (`WeightedDiagonalFunctional.lean`), the same object
`Fermionic.freeGibbsExpectation` already specializes for the fermionic free Boltzmann weight.
`boltzmannWeight energy β n := e^{-βE(n)}` is `diagonalEvolution energy (-β)`'s own diagonal
matrix entries (`matrixCoeff_diagonalEvolution`, proved below), so `diagonalEvolution`-headed
`traceFock`/`gibbsExpectation` and `boltzmannWeight`-headed `weightedTrace`/
`normalizedWeightedDiagonal` are the *same* quantities —
`gibbsExpectation_eq_normalizedWeightedDiagonal` proves it, and `gibbsExpectation` is *defined* as
that specialization directly, so its
linearity/`map_id`/`NormalizedOperatorFunctional` packaging are inherited from
`normalizedWeightedDiagonal`'s existing proofs rather than re-derived.

**`[Fintype Config]` only — deliberately not extended to a `tsum` (bosonic) analogue here.**
Unlike `traceFock`, `tsumTrace` is *not* unconditionally additive on all of `AlgebraicFock Config
→ₗ[ℂ] AlgebraicFock Config` (`tsumTrace_add` needs summability of both operands' diagonal series),
so there is no `tsum` operator space on which a `NormalizedOperatorFunctional` (a genuine
`LinearMap` on *all* operators) can be built the same way. A bosonic normalized expectation is
therefore a fact about *specific* operators with their own summability witnesses (as
`TwoPoint.lean`'s own `tsum` theorem already requires), not a `tsum` specialization of this file's
functional-level abstraction — a structurally different, separate future addition.
-/

namespace SecondQuantization
namespace Common

open scoped Classical

variable {Config : Type*} [Fintype Config]

/-- **The multi-mode free Boltzmann weight**, `e^{-βE(n)}`, generic over the occupation-state type
`Config` and an arbitrary real-valued `energy`. The un-cast-apart form of `diagonalEvolution
energy (-β)`'s own diagonal matrix entries (`matrixCoeff_diagonalEvolution` below) — mirrors
`Fermionic/FreeBoltzmannWeight.lean`'s/`Bosonic/BoltzmannWeightFactorization.lean`'s own
`freeBoltzmannWeight`/`boltzmannWeight`, generalized off the concrete occupation-state type. -/
noncomputable def boltzmannWeight (energy : Config → ℝ) (β : ℝ) (n : Config) : ℂ :=
  Complex.exp (((-β) * energy n : ℝ) : ℂ)

omit [Fintype Config] in
/-- **`diagonalEvolution` is diagonal**: its `(m, n)` matrix entry is `boltzmannWeight` at `m`
when `m = n`, and `0` off the diagonal. -/
theorem matrixCoeff_diagonalEvolution (energy : Config → ℝ) (β : ℝ) (m n : Config) :
    matrixCoeff (diagonalEvolution energy (-β)) m n =
      if m = n then boltzmannWeight energy β m else 0 := by
  rw [matrixCoeff, diagonalEvolution_basisState, boltzmannWeight]
  by_cases h : m = n
  · simp only [if_pos h]
    rw [h, smul_basisState_apply_self]
  · simp only [if_neg h]
    exact smul_basisState_apply_of_ne _ (Ne.symm h)

/-- **`Tr[e^{-βH₀}A] = Tr_{boltzmannWeight}(A)`**: `traceFock` of `diagonalEvolution energy
(-β)`-composed operators is the `boltzmannWeight`-weighted trace, since `diagonalEvolution` is
diagonal with those entries. -/
theorem traceFock_diagonalEvolution_comp_eq_weightedTrace (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock ((diagonalEvolution energy (-β)).comp A) = weightedTrace (boltzmannWeight energy β) A
    := by
  simp only [traceFock, weightedTrace, matrixCoeff_comp, matrixCoeff_diagonalEvolution, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem traceFock_diagonalEvolution_eq_weightSum (energy : Config → ℝ) (β : ℝ) :
    traceFock (diagonalEvolution energy (-β)) = weightSum (boltzmannWeight energy β) := by
  simp only [traceFock, weightSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [matrixCoeff_diagonalEvolution]
  simp

/-- **The normalized Gibbs expectation**, `⟨X⟩ := Tr[e^{-βH₀}X] / Tr[e^{-βH₀}]`, defined directly
as the `boltzmannWeight`-specialization of `Common.normalizedWeightedDiagonal` — see the module
docstring for why this isn't a new abstraction. -/
noncomputable def gibbsExpectation (energy : Config → ℝ) (β : ℝ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) → ℂ :=
  normalizedWeightedDiagonal (boltzmannWeight energy β)

theorem gibbsExpectation_eq_normalizedWeightedDiagonal (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β A = normalizedWeightedDiagonal (boltzmannWeight energy β) A := rfl

theorem gibbsExpectation_id (energy : Config → ℝ) (β : ℝ)
    (hZ : weightSum (boltzmannWeight energy β) ≠ 0) :
    gibbsExpectation energy β
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1 :=
  normalizedWeightedDiagonal_id (boltzmannWeight energy β) hZ

theorem gibbsExpectation_add (energy : Config → ℝ) (β : ℝ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (A + B) =
      gibbsExpectation energy β A + gibbsExpectation energy β B :=
  normalizedWeightedDiagonal_add (boltzmannWeight energy β) A B

theorem gibbsExpectation_smul (energy : Config → ℝ) (β : ℝ) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (c • A) = c * gibbsExpectation energy β A :=
  normalizedWeightedDiagonal_smul c (boltzmannWeight energy β) A

/-- **The normalized Gibbs expectation, packaged as a `Common.NormalizedOperatorFunctional`** —
directly `normalizedWeightedDiagonalFunctional` at `w := boltzmannWeight energy β`. -/
noncomputable def gibbsExpectationFunctional (energy : Config → ℝ) (β : ℝ)
    (hZ : weightSum (boltzmannWeight energy β) ≠ 0) :
    NormalizedOperatorFunctional Config :=
  normalizedWeightedDiagonalFunctional (boltzmannWeight energy β) hZ

/-- **The genuine normalized 2-point Bloch–de Dominicis value**: `⟨C₁Cⱼ⟩ = c₁ⱼ/(1 - ζw₁)`,
dividing `TwoPoint.lean`'s un-normalized `(1 - ζw₁) Tr[e^{-βH₀}(C₁Cⱼ)] = c₁ⱼ Tr[e^{-βH₀}]` through
by the genuine (nonzero) partition function and by the (assumed nonzero) `1 - ζw₁` factor — the
first genuine, normalized-number Bloch–de Dominicis statement, matching the physics reference
notes' `⟨Ĉ₁Ĉⱼ⟩ = C_{1,j}/(1 - ζw₁)` letter-for-letter rather than leaving it as an un-divided trace
equation. -/
theorem gibbsExpectation_comp_eq_div_of_zetaCommutator (energy : Config → ℝ) (β q1 : ℝ)
    (ζ c1j : ℂ) (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp Cj) =
      c1j / (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := traceFock_diagonalEvolution_comp_two_point energy β q1 ζ c1j C1 Cj hC1 hcomm
  rw [gibbsExpectation_eq_normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    ← traceFock_diagonalEvolution_comp_eq_weightedTrace, ← traceFock_diagonalEvolution_eq_weightSum,
    div_eq_div_iff hZ hne]
  linear_combination h

/-- **The normalized 4-point Bloch–de Dominicis *first-operator reduction***, dividing
`FourPointReduction.lean`'s un-normalized `(1 - ζ³w₁) Tr[e^{-βH₀}(C₁C₂C₃C₄)] = c₁₂
Tr[e^{-βH₀}(C₃C₄)] + ζc₁₃ Tr[e^{-βH₀}(C₂C₄)] + ζ²c₁₄ Tr[e^{-βH₀}(C₂C₃)]` through by the genuine
partition function: `⟨C₁C₂C₃C₄⟩ = (c₁₂⟨C₃C₄⟩ + ζc₁₃⟨C₂C₄⟩ + ζ²c₁₄⟨C₂C₃⟩) / (1 - ζ³w₁)`. **Still not
the genuine 4-point *expansion*** (`⟨C₁C₂⟩⟨C₃C₄⟩ + ζ⟨C₁C₃⟩⟨C₂C₄⟩ + ⟨C₁C₄⟩⟨C₂C₃⟩`, a sum of
*products* of normalized 2-point numbers, `gibbsExpectation_four_point` below) — the remaining
`⟨C₃C₄⟩`/`⟨C₂C₄⟩`/`⟨C₂C₃⟩` terms are already normalized 2-point numbers and need no further
reduction; what's missing is only rewriting the *coefficients* `c₁ⱼ/(1-ζw₁)` as `⟨C₁Cⱼ⟩` (via
`gibbsExpectation_comp_eq_div_of_zetaCommutator`, which needs exactly `hC1`/`hcomm1j` — already
supplied here, not new hypotheses on `C₂`/`C₃`/`C₄`) and using `ζ² = 1` (true for `ζ = ±1`, i.e.
`Statistics.zetaInt`) to turn `ζ³` into `ζ` and the trailing `ζ²c₁₄` coefficient into a bare `1`. -/
theorem gibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator (energy : Config → ℝ) (β q1 : ℝ)
    (ζ c12 c13 c14 : ℂ) (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (C2.comp (C3.comp C4))) =
      (c12 * gibbsExpectation energy β (C3.comp C4) +
          ζ * c13 * gibbsExpectation energy β (C2.comp C4) +
          ζ ^ 2 * c14 * gibbsExpectation energy β (C2.comp C3)) /
        (1 - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := traceFock_diagonalEvolution_comp_four_point_reduction energy β q1 ζ c12 c13 c14
    C1 C2 C3 C4 hC1 hcomm12 hcomm13 hcomm14
  have hne' : (1 : ℂ) - ζ ^ 3 * Complex.exp ((β * q1 : ℝ) : ℂ) ≠ 0 := by
    rwa [mul_comm β q1]
  simp only [gibbsExpectation_eq_normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    ← traceFock_diagonalEvolution_comp_eq_weightedTrace, ← traceFock_diagonalEvolution_eq_weightSum]
  field_simp [hne']
  linear_combination (norm := ring_nf) h

/-- **The genuine normalized 4-point Bloch–de Dominicis expansion**: `⟨C₁C₂C₃C₄⟩ = ⟨C₁C₂⟩⟨C₃C₄⟩ +
ζ⟨C₁C₃⟩⟨C₂C₄⟩ + ⟨C₁C₄⟩⟨C₂C₃⟩` (the physics reference notes' `quantum-statistical-mechanics.tex`
example, `for ζ = ±1`) — a product of *normalized 2-point numbers*, obtained from
`gibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator` purely by rewriting each coefficient
`c₁ⱼ/(1-ζw₁)` as `⟨C₁Cⱼ⟩` via `gibbsExpectation_comp_eq_div_of_zetaCommutator` (needing no new
hypotheses on `C₂`/`C₃`/`C₄` — only `hC1`/`hcomm1j`, already present) and using `hζ2 : ζ² = 1` to
collapse `ζ³` to `ζ` and the trailing `ζ²c₁₄` coefficient to `1`. -/
theorem gibbsExpectation_four_point (energy : Config → ℝ) (β q1 : ℝ) (ζ c12 c13 c14 : ℂ)
    (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hζ2 : ζ ^ 2 = 1)
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (C2.comp (C3.comp C4))) =
      gibbsExpectation energy β (C1.comp C2) * gibbsExpectation energy β (C3.comp C4) +
        ζ * gibbsExpectation energy β (C1.comp C3) * gibbsExpectation energy β (C2.comp C4) +
        gibbsExpectation energy β (C1.comp C4) * gibbsExpectation energy β (C2.comp C3) := by
  have hζ3 : ζ ^ 3 = ζ := by
    have h32 : ζ ^ 3 = ζ ^ 2 * ζ := by ring
    rw [h32, hζ2, one_mul]
  have hne3 : (1 : ℂ) - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0 := by rwa [hζ3]
  have h4 := gibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator energy β q1 ζ c12 c13 c14
    C1 C2 C3 C4 hC1 hcomm12 hcomm13 hcomm14 hZ hne3
  rw [hζ3, hζ2] at h4
  have h12 := gibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c12 C1 C2 hC1 hcomm12
    hZ hne
  have h13 := gibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c13 C1 C3 hC1 hcomm13
    hZ hne
  have h14 := gibbsExpectation_comp_eq_div_of_zetaCommutator energy β q1 ζ c14 C1 C4 hC1 hcomm14
    hZ hne
  rw [h4, h12, h13, h14]
  field_simp

/-- **The normalized peel-first identity**, dividing `PeelFirstTrace.lean`'s un-normalized
`(1 - ζ^{l.length}w₁) Tr[e^{-βH₀}(C₁·B₁⋯Bₖ)] = Tr[e^{-βH₀}·peelSum ζ l]` through by the genuine
partition function: `⟨C₁B₁⋯Bₖ⟩ = ⟨peelSum ζ l⟩ / (1 - ζ^{l.length}w₁)`. The general list-indexed
counterpart of `gibbsExpectation_comp_eq_div_of_zetaCommutator`
(`FourPointReduction`/`gibbsExpectation_comp_comp_comp_eq_div_of_zetaCommutator`'s 3-operator case
is a specialization). Not yet decomposed into a `Pairing`-indexed sum — that's the remaining core
of the general `n`-point induction (`Common/BlochDeDominicis/Induction.lean`). -/
theorem gibbsExpectation_peel (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (prodComp (l.map Prod.fst))) =
      gibbsExpectation energy β (peelSum ζ l) / (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ))
    := by
  have h := traceFock_diagonalEvolution_comp_peel energy β q1 ζ C1 l hC1 hcomm
  have hne' : (1 : ℂ) - ζ ^ l.length * Complex.exp ((β * q1 : ℝ) : ℂ) ≠ 0 := by
    rwa [mul_comm β q1]
  simp only [gibbsExpectation_eq_normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    ← traceFock_diagonalEvolution_comp_eq_weightedTrace, ← traceFock_diagonalEvolution_eq_weightSum]
  field_simp [hne']
  linear_combination (norm := ring_nf) h

/-- **`gibbsExpectation` vanishes on `0`** — the missing piece (alongside `gibbsExpectation_add`)
needed to extend additivity from pairs to arbitrary `List.sum`s below. -/
theorem gibbsExpectation_zero (energy : Config → ℝ) (β : ℝ) :
    gibbsExpectation energy β (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 := by
  have h := gibbsExpectation_add energy β
    (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) 0
  simp only [add_zero] at h
  linear_combination -h

/-- **`gibbsExpectation` is additive over `List.sum`s**, not just pairs — needed to distribute it
across `peelSum`'s `List.sum` form (`peelSum_eq_peelTerms_sum`). -/
theorem gibbsExpectation_list_sum (energy : Config → ℝ) (β : ℝ)
    (L : List (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    gibbsExpectation energy β L.sum = (L.map (gibbsExpectation energy β)).sum := by
  induction L with
  | nil => simp [gibbsExpectation_zero]
  | cons A T ih => simp [List.sum_cons, gibbsExpectation_add, ih]

/-- **`gibbsExpectation` of `peelSum`, as an indexed `Finset.sum`**: dividing `peelSum`'s
recursive/`List.sum` structure into its `peelTerms_eq_ofFn`-closed-form individual terms and
applying `gibbsExpectation`'s linearity to each, `⟨peelSum ζ l⟩ = Σⱼ ζʲcⱼ⟨remaining product with
the `j`-th operator erased⟩` — the physics reference notes' `Σⱼ ζʲc₁ⱼ⟨…Ĉⱼ…⟩` presentation, now at
the level of normalized numbers rather than un-normalized traces or a bare `List.sum`. -/
theorem gibbsExpectation_peelSum_eq_sum (energy : Config → ℝ) (β : ℝ) (ζ : ℂ)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ)) :
    gibbsExpectation energy β (peelSum ζ l) =
      ∑ j : Fin l.length, ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2 *
        gibbsExpectation energy β (prodComp ((l.eraseIdx j).map Prod.fst)) := by
  rw [peelSum_eq_peelTerms_sum, peelTerms_eq_ofFn, gibbsExpectation_list_sum, List.map_ofFn,
    List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp, gibbsExpectation_smul, mul_assoc]

/-- **The normalized peel identity, as an indexed `Finset.sum`**: combines `gibbsExpectation_peel`
with `gibbsExpectation_peelSum_eq_sum` to give `⟨C₁B₁⋯Bₖ⟩` directly as a sum of normalized terms
over positions, rather than `⟨peelSum ζ l⟩` left opaque — the piece the general `n`-point induction
(`notes/roadmaps/second-quantization.md`'s Phase 9) actually recurses on. -/
theorem gibbsExpectation_peel_indexed (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp (prodComp (l.map Prod.fst))) =
      (∑ j : Fin l.length, ζ ^ (j : ℕ) * (l[(j : ℕ)]'j.isLt).2 *
          gibbsExpectation energy β (prodComp ((l.eraseIdx j).map Prod.fst))) /
        (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  rw [gibbsExpectation_peel energy β q1 ζ C1 l hC1 hcomm hZ hne, gibbsExpectation_peelSum_eq_sum]

end Common
end SecondQuantization
