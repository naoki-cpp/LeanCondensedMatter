import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import LeanCondensedMatter.SecondQuantization.Bosonic.ParticleNumberWeightSummable
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# The genuine (uncutoff) bosonic 2-point function, from the general Bloch–de Dominicis base case

The bosonic mirror of `Fermionic/BlochDeDominicis/TwoPoint.lean`: the first concrete instantiation
of `Common.tsumTrace_diagonalEvolution_comp_two_point` against real bosonic `annihilate`/`create`
operators. Unlike the fermionic line, `Occupation Mode` is genuinely infinite even for a finite
mode set, so this needs the `tsum`, summability-hypothesis-gated base case rather than the
`[Fintype Config]` one, and the two summability witnesses it asks for are not free: the partition
series (`Bosonic/BoltzmannWeightSummable.lean`) and the rotated two-point double series, the latter
needing the new particle-number-weighted summability fact
(`Bosonic/ParticleNumberWeightSummable.lean`, added specifically for this instantiation) rather
than following automatically the way the fermionic finite-sum case did.

The instantiation uses: `imaginaryTimeEvolve_annihilate`'s eigenvalue-shift fact (`a_i(τ) =
e^{-τεᵢ}a_i`, giving the imaginary-time eigenoperator shift `q := -εᵢ`, which enters the KMS
cyclicity relation) and CCR's `comm_annihilate_create` (the c-number exchange commutator, `ζ :=
+1`). All internal lemmas below work with the Bosonic-local
`imaginaryTimeEvolveFree`/`basisState` (rather than the `Common.diagonalEvolution`/`basisState`
they're literally defined as) purely so `rw`'s syntactic pattern matching lines up with the
`annihilate`/`create` basis-level lemmas — the two forms are definitionally equal, so this makes no
difference where `Common.tsumTrace_diagonalEvolution_comp_two_point` is finally invoked.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode] [Fintype Mode]

/-- **Bridges `Common.matrixCoeff` to the local `basisState`**: `rfl`, stated so every proof below
can start from a `basisState`-headed form the `annihilate`/`create` basis-level lemmas match. -/
private theorem matrixCoeff_eq (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode)
    (m n : Occupation Mode) : Common.matrixCoeff A m n = A (basisState n) m := rfl

private theorem smul_basisState_apply_self (c : ℂ) (n : Occupation Mode) :
    (c • basisState n : FockSpaceBosonic Mode) n = c :=
  Common.smul_basisState_apply_self c n

private theorem smul_basisState_apply_of_ne (c : ℂ) {m n : Occupation Mode} (h : m ≠ n) :
    (c • basisState m : FockSpaceBosonic Mode) n = 0 :=
  Common.smul_basisState_apply_of_ne c h

/-- **The diagonal matrix coefficient of `e^{τH₀}` is its own basis eigenvalue.** -/
theorem matrixCoeff_imaginaryTimeEvolveFree_self (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    Common.matrixCoeff (imaginaryTimeEvolveFree ε τ) n n =
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) := by
  rw [matrixCoeff_eq, imaginaryTimeEvolveFree_basisState, smul_basisState_apply_self]

/-- **The annihilation operator's matrix coefficient against its own lowered state**: `⟨n -
eᵢ|a_i|n⟩ = √(n_i)`, uniformly (`√0 = 0` handles the `n_i = 0` case, where `a_i|n⟩ = 0` anyway). -/
theorem matrixCoeff_annihilate_removeOccupation (i : Mode) (n : Occupation Mode) :
    Common.matrixCoeff (annihilate i) (removeOccupation i n) n = (Real.sqrt (n i : ℝ) : ℂ) := by
  rw [matrixCoeff_eq]
  by_cases h : n i = 0
  · rw [annihilate_basisState_of_zero h, h]
    simp
  · rw [annihilate_basisState_of_pos h, smul_basisState_apply_self]

/-- **The `e^{τH₀}a_i†`-composite's matrix coefficient against a lowered state**: `⟨n|e^{τH₀}a_i†|n
- eᵢ⟩ = √(n_i)e^{τE(n)}`, uniformly (the `n_i = 0` case vanishes on both sides: `√0 = 0` on the
right, and `a_i†|n - eᵢ⟩` lands on a state that differs from `|n⟩` at mode `i` on the left). -/
theorem matrixCoeff_imaginaryTimeEvolveFree_comp_create_removeOccupation
    (ε : Mode → ℝ) (τ : ℝ) (i : Mode) (n : Occupation Mode) :
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε τ).comp (create i)) n (removeOccupation i n) =
      (Real.sqrt (n i : ℝ) : ℂ) * Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) := by
  rw [matrixCoeff_eq, LinearMap.comp_apply, create_basisState_eq, map_smul,
    imaginaryTimeEvolveFree_basisState, smul_smul]
  by_cases h : n i = 0
  · have hrw : removeOccupation i n = n := by
      ext k
      rcases eq_or_ne k i with rfl | hk
      · rw [removeOccupation_apply_same, h]
      · rw [removeOccupation_apply_ne hk]
    have hne : createOccupation i (removeOccupation i n) ≠ n := by
      rw [hrw]
      intro heq
      have hc := createOccupation_apply_same i n
      rw [heq] at hc
      omega
    rw [smul_basisState_apply_of_ne _ hne, h]
    simp
  · have hcoordN : (removeOccupation i n) i + 1 = n i := by
      rw [removeOccupation_apply_same]; omega
    have hcoord : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by exact_mod_cast hcoordN
    rw [createOccupation_removeOccupation_of_pos h, hcoord, smul_basisState_apply_self]

/-- **Off-diagonal (`i ≠ j`) mixed contractions vanish identically**, before any thermal weight is
even involved: the two matrix coefficients' supports are incompatible — `a_i` forces `k =
removeOccupation i n`, but then `e^{τH₀}a_j†` applied at `removeOccupation i n` never lands back on
`n` (its mode-`j` occupation is off by one) since `i ≠ j` leaves mode `j` of `removeOccupation i n`
equal to that of `n`. -/
theorem matrixCoeff_imaginaryTimeEvolveFree_comp_create_mul_matrixCoeff_annihilate_of_ne
    {i j : Mode} (h : i ≠ j) (ε : Mode → ℝ) (τ : ℝ) (n k : Occupation Mode) :
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε τ).comp (create j)) n k *
      Common.matrixCoeff (annihilate i) k n = 0 := by
  by_cases hi : n i = 0
  · have hval : Common.matrixCoeff (annihilate i) k n = 0 := by
      rw [matrixCoeff_eq, annihilate_basisState_of_zero hi]
      simp
    rw [hval, mul_zero]
  · by_cases hk : k = removeOccupation i n
    · subst hk
      have hval : Common.matrixCoeff
          ((imaginaryTimeEvolveFree ε τ).comp (create j)) n (removeOccupation i n) = 0 := by
        rw [matrixCoeff_eq, LinearMap.comp_apply, create_basisState_eq, map_smul,
          imaginaryTimeEvolveFree_basisState, smul_smul]
        have hne : createOccupation j (removeOccupation i n) ≠ n := by
          intro heq
          have hc := createOccupation_apply_same j (removeOccupation i n)
          rw [heq, removeOccupation_apply_ne (Ne.symm h)] at hc
          omega
        rw [smul_basisState_apply_of_ne _ hne]
      rw [hval, zero_mul]
    · have hval : Common.matrixCoeff (annihilate i) k n = 0 := by
        rw [matrixCoeff_eq, annihilate_basisState_of_pos hi,
          smul_basisState_apply_of_ne _ (Ne.symm hk)]
      rw [hval, mul_zero]

/-- **The rotated two-point double series is summable at `i = j`**: it's entirely supported on
`{(n, removeOccupation i n) | n}` (an injective embedding of `Occupation Mode`), where it reduces
to `n_i · e^{-βE(n)}` — exactly `ParticleNumberWeightSummable.lean`'s new summability fact. -/
theorem summable_imaginaryTimeEvolveFree_comp_create_mul_annihilate_diag
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i : Mode) :
    Summable (Function.uncurry (fun n k =>
      Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create i)) n k *
        Common.matrixCoeff (annihilate i) k n)) := by
  set F : Occupation Mode × Occupation Mode → ℂ := Function.uncurry (fun n k =>
    Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create i)) n k *
      Common.matrixCoeff (annihilate i) k n) with hFdef
  set g : Occupation Mode → Occupation Mode × Occupation Mode :=
    fun n => (n, removeOccupation i n) with hgdef
  have hginj : Function.Injective g := fun n n' heq => (Prod.mk.injEq .. ▸ heq).1
  have hvanish : ∀ x ∉ Set.range g, F x = 0 := by
    intro x hx
    by_cases hk : x.2 = removeOccupation i x.1
    · exact absurd ⟨x.1, by simp only [hgdef]; rw [← hk]⟩ hx
    · have hval : Common.matrixCoeff (annihilate i) x.2 x.1 = 0 := by
        by_cases hi : x.1 i = 0
        · rw [matrixCoeff_eq, annihilate_basisState_of_zero hi]; simp
        · rw [matrixCoeff_eq, annihilate_basisState_of_pos hi,
            smul_basisState_apply_of_ne _ (Ne.symm hk)]
      rw [hFdef]
      simp only [Function.uncurry, hval, mul_zero]
  have hcomp : F ∘ g = fun n => (n i : ℂ) *
      Complex.exp ((-β * freeEigenvalue ε n : ℝ) : ℂ) := by
    funext n
    rw [Function.comp_apply, hFdef, hgdef]
    simp only [Function.uncurry]
    rw [matrixCoeff_imaginaryTimeEvolveFree_comp_create_removeOccupation,
      matrixCoeff_annihilate_removeOccupation, mul_right_comm, sqrt_natCast_mul_self]
  rw [← hginj.summable_iff hvanish, hcomp]
  have h := (hasSum_particleNumber_boltzmannWeight ε β hpos i).mapL Complex.ofRealCLM
  have heq : (fun n : Occupation Mode => Complex.ofRealCLM ((n i : ℝ) * boltzmannWeight ε β n)) =
      fun n : Occupation Mode => (n i : ℂ) * Complex.exp ((-β * freeEigenvalue ε n : ℝ) : ℂ) := by
    funext n
    simp [Complex.ofRealCLM_apply, boltzmannWeight]
  rw [heq] at h
  exact h.summable

/-- **The Boltzmann-weighted partition series is summable**, the cast of
`BoltzmannWeightSummable.lean`'s real convergence fact to `ℂ`. -/
theorem summable_imaginaryTimeEvolveFree_self (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) :
    Summable (fun n : Occupation Mode =>
      Common.matrixCoeff (imaginaryTimeEvolveFree ε (-β)) n n) := by
  have h := (hasSum_boltzmannWeight ε β hpos).mapL Complex.ofRealCLM
  have heq : (fun n : Occupation Mode => Complex.ofRealCLM (boltzmannWeight ε β n)) =
      fun n : Occupation Mode => Common.matrixCoeff (imaginaryTimeEvolveFree ε (-β)) n n := by
    funext n
    rw [matrixCoeff_imaginaryTimeEvolveFree_self]
    simp [Complex.ofRealCLM_apply, boltzmannWeight]
  rw [heq] at h
  exact h.summable

/-- **The genuine (uncutoff) bosonic 2-point identity**:
`(1 - e^{-εᵢβ}) Σ'_n ⟨n|e^{-βH₀}(a_ia_j†)|n⟩ = δᵢⱼ Σ'_n ⟨n|e^{-βH₀}|n⟩`, a direct instantiation of
`Common.tsumTrace_diagonalEvolution_comp_two_point` with `C₁ := annihilate i`, `Cⱼ := create j`,
`q₁ := -εᵢ` (from `imaginaryTimeEvolve_annihilate`), and `ζ := +1`, `c₁ⱼ := δᵢⱼ` (from CCR's
`comm_annihilate_create`), given every mode's one-mode convergence condition `0 < βεᵢ`. After
dividing by the partition function (not done here — would need
`tsum_boltzmannWeight_ne_zero`'s non-vanishing), the `i = j` case gives `⟨aᵢaᵢ†⟩_β = 1/(1-e^{-βεᵢ})
= 1 + n_B(εᵢ)`; only after further using `aᵢaᵢ† = Nᵢ + 1` (not proved here either — no bosonic
`numberOperator` API yet) does this become the Bose–Einstein occupation number itself,
`⟨Nᵢ⟩_β = 1/(e^{βεᵢ}-1) = n_B(εᵢ)`. -/
theorem tsumTrace_imaginaryTimeEvolveFree_comp_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ k, 0 < β * ε k) (i j : Mode) :
    (1 - Complex.exp ((-(ε i) * β : ℝ) : ℂ)) *
        Common.tsumTrace
          ((imaginaryTimeEvolveFree ε (-β)).comp ((annihilate i).comp (create j))) =
      (if i = j then (1 : ℂ) else 0) * Common.tsumTrace (imaginaryTimeEvolveFree ε (-β)) := by
  unfold imaginaryTimeEvolveFree
  have hC1 : Common.heisenbergEvolve (freeEigenvalue ε) (-β) (annihilate i) =
      Complex.exp ((-(ε i) * (-β) : ℝ) : ℂ) • annihilate i := by
    have h := imaginaryTimeEvolve_annihilate ε (-β) i
    rwa [show ((-(ε i) * (-β) : ℝ) : ℂ) = -((-β : ℝ) : ℂ) * (ε i : ℂ) by push_cast; ring]
  have hcomm : (annihilate i).comp (create j) -
      (1 : ℂ) • ((create j).comp (annihilate i)) =
        (if i = j then (1 : ℂ) else 0) •
          (LinearMap.id : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) := by
    rw [one_smul]
    have h := comm_annihilate_create i j
    rw [comm] at h
    rw [h]
    split_ifs <;> simp
  have hSummD := summable_imaginaryTimeEvolveFree_self ε β hpos
  by_cases hij : i = j
  · subst hij
    have h := summable_imaginaryTimeEvolveFree_comp_create_mul_annihilate_diag ε β hpos i
    have hthm := Common.tsumTrace_diagonalEvolution_comp_two_point (freeEigenvalue ε) β (-(ε i))
      (1 : ℂ) (if i = i then (1 : ℂ) else 0) (annihilate i) (create i) hC1 hcomm hSummD h
    simpa using hthm
  · have hzero : Function.uncurry (fun n k =>
        Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create j)) n k *
          Common.matrixCoeff (annihilate i) k n) = 0 := by
      funext p
      simp only [Function.uncurry, Pi.zero_apply]
      exact matrixCoeff_imaginaryTimeEvolveFree_comp_create_mul_matrixCoeff_annihilate_of_ne hij ε
        (-β) p.1 p.2
    have h : Summable (Function.uncurry (fun n k =>
        Common.matrixCoeff ((imaginaryTimeEvolveFree ε (-β)).comp (create j)) n k *
          Common.matrixCoeff (annihilate i) k n)) := by
      rw [hzero]; exact summable_zero
    have hthm := Common.tsumTrace_diagonalEvolution_comp_two_point (freeEigenvalue ε) β (-(ε i))
      (1 : ℂ) (if i = j then (1 : ℂ) else 0) (annihilate i) (create j) hC1 hcomm hSummD h
    simpa using hthm

end Bosonic
end SecondQuantization
