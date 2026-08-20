import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.LegFamily
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst

set_option linter.style.header false

/-!
# Dyson diagram expansion: operator flattening
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Flattening `nestedVertexOperatorComp` into a `4n`-atom `Common.prodComp` -/

omit [LinearOrder Mode] [Fintype Mode] in
/-- **`imaginaryTimeEvolve` distributes over composition** — directly
`Common.heisenbergEvolve_comp` at `energy := fermionEnergy ε`. Needed to unfold
`quarticVertexOperator`'s evolution atom-by-atom. -/
theorem imaginaryTimeEvolve_comp (ε : Mode → ℝ) (τ : ℝ)
    (A B : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    imaginaryTimeEvolve ε τ (A.comp B) =
      (imaginaryTimeEvolve ε τ A).comp (imaginaryTimeEvolve ε τ B) :=
  Common.heisenbergEvolve_comp (fermionEnergy ε) τ A B

omit [Fintype Mode] in
/-- **A single vertex's evolved operator, flattened into a `Common.prodComp` of its four
individually-evolved atomic legs**: unfolds `quarticVertexOperator`'s own definition
(`c₁† c₂† a₂ a₁`) via `imaginaryTimeEvolve_comp`, three times, matching
`quarticLocalLegOperator`'s `0 ↦ create₁, 1 ↦ create₂, 2 ↦ annihilate₂, 3 ↦ annihilate₁`
convention exactly. -/
theorem interactionPicture_quarticVertexOperator_eq_prodComp (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      Common.prodComp
        (List.ofFn (fun l : Fin 4 => imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l))) := by
  change imaginaryTimeEvolve ε τ (quarticVertexOperator q) = _
  rw [quarticVertexOperator, imaginaryTimeEvolve_comp, imaginaryTimeEvolve_comp,
    imaginaryTimeEvolve_comp]
  simp [Common.prodComp, quarticLocalLegOperator, List.ofFn_succ]

omit [Fintype Mode] in
/-- **A flattened leg's evolution eigenvalue shift** — `quarticLocalLegEnergyShift` at the vertex
label and local leg selected by the Common quartic flattening coordinates. Named so the general
theorem's own `q : Fin (2 * (2 * n)) → ℝ` eigenvalue-shift family can be stated as
`flatVertexLegEnergyShift ε q` directly. -/
noncomputable def flatVertexLegEnergyShift {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (p : Fin (2 * (2 * n))) : ℝ :=
  quarticLocalLegEnergyShift ε (q (flatVertexIndex n p)) (flatLocalLeg n p)

omit [Fintype Mode] in
/-- **Every flattened leg operator is, up to its own `Complex.exp` eigenvalue-shift scalar, a bare
atomic `quarticLocalLegOperator`** — the normal form both
`heisenbergEvolve_quarticLegOperatorForSequence` and `zetaCommutator_quarticLegOperatorForSequence`
reduce to before invoking, respectively,
`heisenbergEvolve_imaginaryTimeEvolve_quarticLocalLegOperator`/`Common.zetaCommutator_smul_smul`. -/
theorem quarticLegOperatorForSequence_eq_smul {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    quarticLegOperatorForSequence ε q τ p =
      Complex.exp ((τ (flatVertexIndex n p) * flatVertexLegEnergyShift ε q p : ℝ) : ℂ) •
        quarticLocalLegOperator (q (flatVertexIndex n p)) (flatLocalLeg n p) := by
  rw [quarticLegOperatorForSequence, imaginaryTimeEvolve_quarticLocalLegOperator]
  rfl

omit [Fintype Mode] in
theorem quarticLegOperatorForSequence_cast_mul_add {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (i : Fin n) (j : Fin 4)
    (h : 2 * (2 * n) = n * 4) :
    quarticLegOperatorForSequence ε q τ (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩) =
      imaginaryTimeEvolve ε (τ i) (quarticLocalLegOperator (q i) j) := by
  rw [quarticLegOperatorForSequence, Common.orderedQuarticLegEquiv_cast_mul_add i j h]

omit [Fintype Mode] in
/-- **A single evolved atomic leg operator is an eigenoperator of `heisenbergEvolve (fermionEnergy
ε) (-β)`, with an eigenvalue shift *independent of the dressing time* `τ`** — the fact the general
Bloch–de Dominicis theorem's own eigenoperator hypothesis needs, for each of the `4n` legs
`quarticLegOperatorForSequence` produces. Proved via `Common.heisenbergEvolve_heisenbergEvolve`
(the two evolutions, at `τ` and `-β`, combine into a single evolution at `τ + (-β)`) and
`imaginaryTimeEvolve_quarticLocalLegOperator` (applied twice: once at `τ + (-β)` to evaluate the
combined evolution, once at `τ` in reverse to factor the `τ`-dependent piece back out) — the two
resulting `Complex.exp`s combine via `exp_add`/`ring`, leaving only the `-β`-dependent factor. -/
theorem heisenbergEvolve_imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ) (β : ℝ)
    (q : QuarticVertexLabel Mode) (l : Fin 4) (τ : ℝ) :
    Common.heisenbergEvolve (fermionEnergy ε) (-β)
        (imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l)) =
      Complex.exp (((quarticLocalLegEnergyShift ε q l * (-β) : ℝ)) : ℂ) •
        imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) := by
  have step : Common.heisenbergEvolve (fermionEnergy ε) (-β)
      (imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l)) =
      imaginaryTimeEvolve ε (τ + -β) (quarticLocalLegOperator q l) :=
    Common.heisenbergEvolve_heisenbergEvolve (fermionEnergy ε) τ (-β)
      (quarticLocalLegOperator q l)
  rw [step, imaginaryTimeEvolve_quarticLocalLegOperator,
    imaginaryTimeEvolve_quarticLocalLegOperator, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

omit [Fintype Mode] in
/-- **Every atomic leg operator `quarticLegOperatorForSequence` produces is an eigenoperator of
`heisenbergEvolve (fermionEnergy ε) (-β)`** — direct specialization of
`heisenbergEvolve_imaginaryTimeEvolve_quarticLocalLegOperator` to the flattened position `p`'s own
vertex label and time assignment. -/
theorem heisenbergEvolve_quarticLegOperatorForSequence {n : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    Common.heisenbergEvolve (fermionEnergy ε) (-β) (quarticLegOperatorForSequence ε q τ p) =
      Complex.exp ((flatVertexLegEnergyShift ε q p * (-β) : ℝ) : ℂ) •
        quarticLegOperatorForSequence ε q τ p :=
  heisenbergEvolve_imaginaryTimeEvolve_quarticLocalLegOperator ε β
    (q (flatVertexIndex n p)) (flatLocalLeg n p) (τ (flatVertexIndex n p))

omit [Fintype Mode] in
/-- **`nestedVertexOperatorComp`, flattened into a `Common.prodComp` of its `4n` atomic legs** —
by induction on `n`: the base case is trivial (`Fin (2 * (2 * 0))` is empty); the successor case
reduces, via `nestedVertexOperatorComp_succ`,
`interactionPicture_quarticVertexOperator_eq_prodComp`, the inductive hypothesis, and
`Common.prodComp_append`, to the *pure list* equality `List.ofFn (quarticLegOperatorForSequence ε
q τ) = List.ofFn (4 atoms for vertex 0) ++ List.ofFn (quarticLegOperatorForSequence ε (tail q)
(tail τ))`, proved via `List.ofFn_fin_append`/`Fin.addCases` splitting the domain additively into
`4 + 2 * (2 * n)`: the `left` branch matches `quarticLegOperatorForSequence_cast_mul_add` at
vertex `0` directly; the `right` branch uses the Common
`eq_cast_mul_add_orderedQuarticLegEquiv` to express an *arbitrary* position `k` of the smaller
`n`-fold piece in `i' * 4 + j'` form, then matches both sides via
`quarticLegOperatorForSequence_cast_mul_add` (at `n` for the RHS, at `n + 1` and vertex `i'.succ`
for the LHS) — the two positions agree because `4 + (i' * 4 + j') = i'.succ * 4 + j'` as
naturals. -/
theorem prodComp_ofFn_quarticLegOperatorForSequence_eq_nestedVertexOperatorComp (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ),
      Common.prodComp (List.ofFn (quarticLegOperatorForSequence ε q τ)) =
        nestedVertexOperatorComp ε n q τ
  | 0, q, τ => by
    have h0 : 2 * (2 * 0) = 0 := by ring
    have : IsEmpty (Fin (2 * (2 * 0))) := h0 ▸ Fin.isEmpty
    simp [List.ofFn]
  | n + 1, q, τ => by
    have hcard : 2 * (2 * (n + 1)) = (n + 1) * 4 := by ring
    have hcard' : 2 * (2 * n) = n * 4 := by ring
    have h2 : 2 * (2 * (n + 1)) = 4 + 2 * (2 * n) := by ring
    rw [nestedVertexOperatorComp_succ, interactionPicture_quarticVertexOperator_eq_prodComp,
      ← prodComp_ofFn_quarticLegOperatorForSequence_eq_nestedVertexOperatorComp ε n
        (fun i => q i.succ) (fun i => τ i.succ),
      ← Common.prodComp_append, List.ofFn_congr h2, ← List.ofFn_fin_append]
    refine congrArg Common.prodComp
      (congrArg List.ofFn (funext (Fin.addCases (fun j => ?_) fun k => ?_)))
    · have e1 : Fin.cast h2.symm (Fin.castAdd (2 * (2 * n)) j) =
          Fin.cast hcard.symm ⟨((0 : Fin (n + 1)) : ℕ) * 4 + (j : ℕ), by omega⟩ := by
        apply Fin.ext
        simp
      change quarticLegOperatorForSequence ε q τ (Fin.cast h2.symm (Fin.castAdd _ j)) =
        Fin.append (fun j : Fin 4 => imaginaryTimeEvolve ε (τ 0) (quarticLocalLegOperator (q 0) j))
          (quarticLegOperatorForSequence ε (fun i => q i.succ) (fun i => τ i.succ))
          (Fin.castAdd _ j)
      rw [Fin.append_left, e1, quarticLegOperatorForSequence_cast_mul_add ε q τ 0 j hcard]
    · have hk := Common.eq_cast_mul_add_orderedQuarticLegEquiv k hcard'
      have e2 : Fin.cast h2.symm (Fin.natAdd 4 k) = Fin.cast hcard.symm
          ⟨((Common.orderedQuarticLegEquiv n k).1.succ : ℕ) * 4 +
              ((Common.orderedQuarticLegEquiv n k).2 : ℕ),
            by
              have := (Common.orderedQuarticLegEquiv n k).2.isLt
              omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
        have hkval : (k : ℕ) =
            (Common.orderedQuarticLegEquiv n k).1 * 4 + (Common.orderedQuarticLegEquiv n k).2 := by
          have := congrArg Fin.val hk
          simpa using this
        omega
      change quarticLegOperatorForSequence ε q τ (Fin.cast h2.symm (Fin.natAdd 4 k)) =
        Fin.append (fun j : Fin 4 => imaginaryTimeEvolve ε (τ 0) (quarticLocalLegOperator (q 0) j))
          (quarticLegOperatorForSequence ε (fun i => q i.succ) (fun i => τ i.succ))
          (Fin.natAdd 4 k)
      rw [Fin.append_right, e2,
        quarticLegOperatorForSequence_cast_mul_add ε q τ
          (Common.orderedQuarticLegEquiv n k).1.succ
          (Common.orderedQuarticLegEquiv n k).2 hcard]
      have hrest := quarticLegOperatorForSequence_cast_mul_add ε
        (fun i => q i.succ) (fun i => τ i.succ)
        (Common.orderedQuarticLegEquiv n k).1 (Common.orderedQuarticLegEquiv n k).2 hcard'
      rw [← hk] at hrest
      exact hrest.symm

/-! ## The general theorem's zeta-commutator hypothesis, for the full evolved `4n`-leg family

The bare single-vertex-four-legs case (`quarticLocalLegMode`, `quarticLocalLegIsCreate`,
`anticomm_quarticLocalLegOperator`, `zetaCommutator_quarticLocalLegOperator`) now lives in
`QuarticLocalLeg.lean`. -/

omit [Fintype Mode] in
/-- **The general theorem's `c i j` coefficient family**, for the evolved, flattened `4n`-leg
family — the product of both legs' `Complex.exp` eigenvalue-shift scalars and the bare
single-vertex commutator indicator (`quarticLocalLegIsCreate`/`quarticLocalLegMode`-based), exactly
what `zetaCommutator_quarticLegOperatorForSequence` computes `Common.zetaCommutator` to equal.
Naming this family is what lets the eventual
`Common.BlochDeDominicis.finiteGibbsExpectation_prodComp_eq_sum_pairing`
application read as passing three named families (`quarticLegOperatorForSequence ε q τ`,
`flatVertexLegEnergyShift ε q`, `flatVertexLegCommutatorCoeff ε q τ`) rather than three copies of
the same inlined case analysis. -/
noncomputable def flatVertexLegCommutatorCoeff {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p p' : Fin (2 * (2 * n))) : ℂ :=
  Complex.exp ((τ (flatVertexIndex n p) * flatVertexLegEnergyShift ε q p : ℝ) : ℂ) *
    Complex.exp ((τ (flatVertexIndex n p') * flatVertexLegEnergyShift ε q p' : ℝ) : ℂ) *
    (if quarticLocalLegIsCreate (flatLocalLeg n p) = quarticLocalLegIsCreate (flatLocalLeg n p')
      then (0 : ℂ)
     else if quarticLocalLegMode (q (flatVertexIndex n p)) (flatLocalLeg n p) =
        quarticLocalLegMode (q (flatVertexIndex n p')) (flatLocalLeg n p') then 1
     else 0)

omit [Fintype Mode] in
/-- **The general theorem's zeta-commutator hypothesis, for two arbitrary evolved/flattened leg
positions** — combines `quarticLegOperatorForSequence_eq_smul` (reducing each evolved leg to a
bare `quarticLocalLegOperator` times its own `Complex.exp` eigenvalue-shift scalar),
`Common.zetaCommutator_smul_smul` (pulling both scalars out of the commutator as a product), and
`zetaCommutator_quarticLocalLegOperator` (the bare single-vertex commutator constant) into
`flatVertexLegCommutatorCoeff`, now valid for *any* pair of flattened positions `p, p'` —
same-vertex or cross-vertex alike, since the underlying
`quarticLocalLegOperator`/`quarticLocalLegMode`/`quarticLocalLegIsCreate` machinery never assumed a
shared vertex. -/
theorem zetaCommutator_quarticLegOperatorForSequence {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p p' : Fin (2 * (2 * n))) :
    Common.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (quarticLegOperatorForSequence ε q τ p) (quarticLegOperatorForSequence ε q τ p') =
      flatVertexLegCommutatorCoeff ε q τ p p' •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  rw [quarticLegOperatorForSequence_eq_smul, quarticLegOperatorForSequence_eq_smul,
    Common.zetaCommutator_smul_smul, zetaCommutator_quarticLocalLegOperator, smul_smul,
    flatVertexLegCommutatorCoeff]

/-! ## The general theorem's non-resonance hypothesis -/

/-- **The general theorem's third (non-resonance) hypothesis is automatic for fermions, at any real
eigenvalue shift** — `Common.Statistics.fermion.zetaInt = -1` turns `1 - ζ * exp(x * β)` into
`1 + exp(x * β)`, and `Complex.exp` at a real argument is a positive real number, so this can never
vanish. Unlike the eigenoperator/commutator hypotheses, this one needs no information about the
`quarticLegOperatorForSequence` family at all — it holds for *every* real `x`, `β`. -/
theorem one_sub_zetaInt_fermion_mul_exp_ne_zero (x β : ℝ) :
    (1 : ℂ) - ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ) * Complex.exp ((x * β : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < 1 + Real.exp (x * β) := by
    positivity
  have heq : (1 : ℂ) - ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ) *
      Complex.exp ((x * β : ℝ) : ℂ) = ((1 + Real.exp (x * β) : ℝ) : ℂ) := by
    rw [Common.Statistics.zetaInt_fermion]
    push_cast [Complex.ofReal_exp]
    ring
  rw [heq]
  exact_mod_cast hpos.ne'

omit [Fintype Mode] [LinearOrder Mode] in
/-- **The general theorem's non-resonance hypothesis, for every flattened leg position** — direct
specialization of `one_sub_zetaInt_fermion_mul_exp_ne_zero` to `x := flatVertexLegEnergyShift ε q
p`. This is the *third and final* hypothesis
`Common.BlochDeDominicis.finiteGibbsExpectation_prodComp_eq_sum_pairing` needs; combined with
`heisenbergEvolve_quarticLegOperatorForSequence` and
`zetaCommutator_quarticLegOperatorForSequence`, the general theorem can now be applied to the
flattened `4n`-leg family. -/
theorem one_sub_zetaInt_fermion_mul_exp_flatVertexLegEnergyShift_ne_zero {n : ℕ} (ε : Mode → ℝ)
    (β : ℝ) (q : Fin n → QuarticVertexLabel Mode) (p : Fin (2 * (2 * n))) :
    (1 : ℂ) - ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ) *
        Complex.exp ((flatVertexLegEnergyShift ε q p * β : ℝ) : ℂ) ≠ 0 :=
  one_sub_zetaInt_fermion_mul_exp_ne_zero (flatVertexLegEnergyShift ε q p) β

end Fermionic
end SecondQuantization
