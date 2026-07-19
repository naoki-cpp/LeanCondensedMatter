import LeanCondensedMatter.SecondQuantization.Common.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# The KMS-type trace rotation, combining trace cyclicity and the KMS-type relation

Phase 9, step 4 of Track D's finite-mode fermionic primary line
(`notes/roadmaps/second-quantization.md`), step 3 of the plan (discussed with the user) toward a
common `Common/`-level Bloch–de Dominicis induction interface usable by both statistics: combines
`Common.traceFock_comp_comm` (trace cyclicity, `[Fintype Config]`) with
`Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution` (the KMS-type relation) into the
single identity the theorem's induction actually uses to move a ladder operator from the end of an
operator product to its front, picking up an eigenvalue-dependent weight:

`Tr[e^{-βH₀} (A C)] = e^{qβ} Tr[e^{-βH₀} (C A)]`

matching the physics reference notes' derivation (`quantum-statistical-mechanics.tex`, the
`⟨Ĉ₂⋯Ĉ_{2n}Ĉ₁⟩ = w₁⟨Ĉ₁Ĉ₂⋯Ĉ_{2n}⟩` step inside the Bloch–de Dominicis theorem's proof) exactly:
`A` plays the role of `Ĉ₂⋯Ĉ_{2n}`, `C` plays the role of `Ĉ₁`, and `w₁ = e^{qβ}` is `C`'s
eigenvalue-shift weight (`q = -εᵢ` for `annihilate i`, `q = εᵢ` for `create i`).

**Still `[Fintype Config]`-gated** (via `traceFock_comp_comm`), so — as with `traceFock_comp_comm`
itself — this is fermionic-usable now; a bosonic analogue needs the `tsum`-summability-gated
`Common.tsum_matrixCoeff_diag_comp_comm` in place of `traceFock_comp_comm`, not supplied here.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

omit [Fintype Config] in
/-- **`C e^{τH₀} = e^{-qτ} e^{τH₀} C`**, the KMS-type relation with `C` on the left — the algebraic
rearrangement of `diagonalEvolution_comp_eq_smul_comp_diagonalEvolution` needed by
`traceFock_diagonalEvolution_comp_rotate` below, obtained by multiplying both sides of that lemma
by the (nonzero) reciprocal exponential factor. -/
theorem comp_diagonalEvolution_eq_smul_diagonalEvolution_comp
    (energy : Config → ℝ) (τ q : ℝ) (C : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC : heisenbergEvolve energy τ C = Complex.exp ((q * τ : ℝ) : ℂ) • C) :
    C.comp (diagonalEvolution energy τ) =
      Complex.exp ((-(q * τ) : ℝ) : ℂ) • ((diagonalEvolution energy τ).comp C) := by
  have hKMS := diagonalEvolution_comp_eq_smul_comp_diagonalEvolution energy τ q C hC
  have h2 := congrArg (fun x => Complex.exp ((-(q * τ) : ℝ) : ℂ) • x) hKMS
  simp only [smul_smul] at h2
  rw [show Complex.exp ((-(q * τ) : ℝ) : ℂ) * Complex.exp ((q * τ : ℝ) : ℂ) = 1 by
    rw [← Complex.exp_add, ← Complex.ofReal_add]; norm_num, one_smul] at h2
  exact h2.symm

/-- **The KMS-type trace rotation**: `Tr[e^{-βH₀} (A C)] = e^{qβ} Tr[e^{-βH₀} (C A)]`, for any
operator `A` and any operator `C` with eigenvalue-shift `q` under `heisenbergEvolve`. Combines
`traceFock_comp_comm` (cyclicity) with `comp_diagonalEvolution_eq_smul_diagonalEvolution_comp` (the
KMS-type relation) exactly as the physics reference notes' `⟨Ĉ₂⋯Ĉ_{2n}Ĉ₁⟩ = w₁⟨Ĉ₁Ĉ₂⋯Ĉ_{2n}⟩` step
does. -/
theorem traceFock_diagonalEvolution_comp_rotate
    (energy : Config → ℝ) (β q : ℝ) (A C : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC : heisenbergEvolve energy (-β) C = Complex.exp ((q * (-β) : ℝ) : ℂ) • C) :
    traceFock ((diagonalEvolution energy (-β)).comp (A.comp C)) =
      Complex.exp ((q * β : ℝ) : ℂ) •
        traceFock ((diagonalEvolution energy (-β)).comp (C.comp A)) := by
  have hKMS' := comp_diagonalEvolution_eq_smul_diagonalEvolution_comp energy (-β) q C hC
  rw [show ((-(q * -β) : ℝ) : ℂ) = ((q * β : ℝ) : ℂ) by push_cast; ring] at hKMS'
  calc traceFock ((diagonalEvolution energy (-β)).comp (A.comp C))
      = traceFock (((diagonalEvolution energy (-β)).comp A).comp C) := by
        rw [LinearMap.comp_assoc]
    _ = traceFock (C.comp ((diagonalEvolution energy (-β)).comp A)) := traceFock_comp_comm _ _
    _ = traceFock ((C.comp (diagonalEvolution energy (-β))).comp A) := by
        rw [LinearMap.comp_assoc]
    _ = traceFock ((Complex.exp ((q * β : ℝ) : ℂ) •
          ((diagonalEvolution energy (-β)).comp C)).comp A) := by rw [hKMS']
    _ = traceFock (Complex.exp ((q * β : ℝ) : ℂ) •
          (((diagonalEvolution energy (-β)).comp C).comp A)) := by rw [LinearMap.smul_comp]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          traceFock (((diagonalEvolution energy (-β)).comp C).comp A) := by
        rw [traceFock_smul, smul_eq_mul]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          traceFock ((diagonalEvolution energy (-β)).comp (C.comp A)) := by
        rw [LinearMap.comp_assoc]

/-! ## The 2-point base case of the Bloch–de Dominicis induction -/

/-- **The 2-point Bloch–de Dominicis base case**: `(1 - ζw₁) ⟨C₁Cⱼ⟩ = c₁ⱼ ⟨id⟩`, where `⟨X⟩ :=
Tr[e^{-βH₀}X]`, `c₁ⱼ` is the (assumed scalar) `ζ`-commutator `[C₁, Cⱼ]_ζ := C₁Cⱼ - ζCⱼC₁`, and `w₁
:= e^{q₁β}` is `C₁`'s KMS weight (`q₁` its eigenvalue shift). This is the un-normalized,
un-divided form of the physics reference notes' `⟨Ĉ₁Ĉⱼ⟩ = C_{1,j}/(1 - ζw₁)`
(`quantum-statistical-mechanics.tex`, the `n = 1` base case inside the general Bloch–de Dominicis
induction): derived from the assumed c-number commutator (rewriting `C₁Cⱼ` as `c₁ⱼ • id + ζ•(CⱼC₁)`)
and `traceFock_diagonalEvolution_comp_rotate` (rotating `CⱼC₁` back to `w₁•(C₁Cⱼ)`), then solving
the resulting self-referential equation for the trace — left un-divided (rather than requiring
`1 - ζw₁ ≠ 0` as a further hypothesis) so the caller decides how to use it. -/
theorem traceFock_diagonalEvolution_comp_two_point
    (energy : Config → ℝ) (β q1 : ℝ) (ζ c1j : ℂ)
    (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        traceFock ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) =
      c1j * traceFock (diagonalEvolution energy (-β)) := by
  rw [sub_eq_iff_eq_add] at hcomm
  have hrot := traceFock_diagonalEvolution_comp_rotate energy β q1 Cj C1 hC1
  have hstep : traceFock ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) =
      c1j * traceFock (diagonalEvolution energy (-β)) +
        ζ * traceFock ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) := by
    conv_lhs => rw [hcomm]
    rw [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.comp_smul, LinearMap.comp_id,
      traceFock_add, traceFock_smul, traceFock_smul]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

/-! ## The `tsum` (possibly-infinite-`Config`) versions -/

variable {Config' : Type*}

/-- **The `tsum` KMS-type trace rotation**: the `[Fintype Config]`-free analogue of
`traceFock_diagonalEvolution_comp_rotate`, built from `tsum_matrixCoeff_diag_comp_comm`
(`Common/WeightedDiagonalFunctional.lean`'s summability-gated `tsum` cyclicity) instead of
`traceFock_comp_comm`. This is the piece that lets the rotation step — hence, eventually, the
2-point base case and the general induction — reach a genuine bosonic occupation type, at the cost
of the explicit double-summability hypothesis `h` (unlike the `[Fintype Config]` case, where it is
automatic). -/
theorem tsum_matrixCoeff_diag_diagonalEvolution_comp_rotate
    (energy : Config' → ℝ) (β q : ℝ) (A C : AlgebraicFock Config' →ₗ[ℂ] AlgebraicFock Config')
    (hC : heisenbergEvolve energy (-β) C = Complex.exp ((q * (-β) : ℝ) : ℂ) • C)
    (h : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp A) n k * matrixCoeff C k n))) :
    ∑' n, matrixCoeff ((diagonalEvolution energy (-β)).comp (A.comp C)) n n =
      Complex.exp ((q * β : ℝ) : ℂ) •
        ∑' n, matrixCoeff ((diagonalEvolution energy (-β)).comp (C.comp A)) n n := by
  have hKMS' := comp_diagonalEvolution_eq_smul_diagonalEvolution_comp energy (-β) q C hC
  rw [show ((-(q * -β) : ℝ) : ℂ) = ((q * β : ℝ) : ℂ) by push_cast; ring] at hKMS'
  have hcyc := tsum_matrixCoeff_diag_comp_comm ((diagonalEvolution energy (-β)).comp A) C h
  have hsmul : (fun n => matrixCoeff (Complex.exp ((q * β : ℝ) : ℂ) •
        (((diagonalEvolution energy (-β)).comp C).comp A)) n n) =
      fun n => Complex.exp ((q * β : ℝ) : ℂ) *
        matrixCoeff (((diagonalEvolution energy (-β)).comp C).comp A) n n :=
    funext fun n => matrixCoeff_smul _ _ n n
  calc ∑' n, matrixCoeff ((diagonalEvolution energy (-β)).comp (A.comp C)) n n
      = ∑' n, matrixCoeff (((diagonalEvolution energy (-β)).comp A).comp C) n n := by
        rw [LinearMap.comp_assoc]
    _ = ∑' n, matrixCoeff (C.comp ((diagonalEvolution energy (-β)).comp A)) n n := hcyc
    _ = ∑' n, matrixCoeff ((C.comp (diagonalEvolution energy (-β))).comp A) n n := by
        rw [LinearMap.comp_assoc]
    _ = ∑' n, matrixCoeff ((Complex.exp ((q * β : ℝ) : ℂ) •
          ((diagonalEvolution energy (-β)).comp C)).comp A) n n := by rw [hKMS']
    _ = ∑' n, matrixCoeff (Complex.exp ((q * β : ℝ) : ℂ) •
          (((diagonalEvolution energy (-β)).comp C).comp A)) n n := by rw [LinearMap.smul_comp]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          ∑' n, matrixCoeff (((diagonalEvolution energy (-β)).comp C).comp A) n n := by
        rw [hsmul, tsum_mul_left, smul_eq_mul]
    _ = Complex.exp ((q * β : ℝ) : ℂ) •
          ∑' n, matrixCoeff ((diagonalEvolution energy (-β)).comp (C.comp A)) n n := by
        rw [LinearMap.comp_assoc]

/-- **The `tsum` 2-point Bloch–de Dominicis base case**: the `[Fintype Config]`-free analogue of
`traceFock_diagonalEvolution_comp_two_point`, given the same c-number-commutator and KMS-weight
hypotheses plus explicit summability of `C₁`'s and `Cⱼ`'s diagonal series (`hSummD`,
`hSummDCjC1`) and of the rotation's double series (`h`). This is the theorem a genuine bosonic
free Boltzmann weight would need to instantiate (supplying all three summability witnesses from
`Bosonic/BoltzmannWeightSummable.lean`-style convergence facts, not done here) to get a real
bosonic 2-point function out of this framework. -/
theorem tsum_matrixCoeff_diag_diagonalEvolution_comp_two_point
    (energy : Config' → ℝ) (β q1 : ℝ) (ζ c1j : ℂ)
    (C1 Cj : AlgebraicFock Config' →ₗ[ℂ] AlgebraicFock Config')
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config' →ₗ[ℂ] AlgebraicFock Config'))
    (hSummD : Summable (fun n => matrixCoeff (diagonalEvolution energy (-β)) n n))
    (hSummDCjC1 : Summable
      (fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) n n))
    (h : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp Cj) n k * matrixCoeff C1 k n))) :
    (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        ∑' n, matrixCoeff ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) n n =
      c1j * ∑' n, matrixCoeff (diagonalEvolution energy (-β)) n n := by
  rw [sub_eq_iff_eq_add] at hcomm
  have hrot := tsum_matrixCoeff_diag_diagonalEvolution_comp_rotate energy β q1 Cj C1 hC1 h
  have hstep : ∑' n, matrixCoeff ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) n n =
      c1j * ∑' n, matrixCoeff (diagonalEvolution energy (-β)) n n +
        ζ * ∑' n, matrixCoeff ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) n n := by
    have hpoint : (fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) n n) =
        fun n => c1j * matrixCoeff (diagonalEvolution energy (-β)) n n +
          ζ * matrixCoeff ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) n n := by
      funext n
      conv_lhs => rw [hcomm]
      rw [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.comp_smul, LinearMap.comp_id,
        matrixCoeff_add, matrixCoeff_smul, matrixCoeff_smul]
    rw [hpoint]
    have h1 : Summable (fun n => c1j * matrixCoeff (diagonalEvolution energy (-β)) n n) :=
      hSummD.mul_left c1j
    have h2 : Summable
        (fun n => ζ * matrixCoeff ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) n n) :=
      hSummDCjC1.mul_left ζ
    rw [(h1.hasSum.add h2.hasSum).tsum_eq, tsum_mul_left, tsum_mul_left]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

end Common
end SecondQuantization
