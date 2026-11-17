import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Diagonal
import LeanCondensedMatter.Analysis.Operator.Diagonal
import Mathlib.Order.Filter.Finite

set_option linter.style.header false

/-!
# Coordinate projections on completed Fock space

A predicate on configurations determines a contractive coordinate projection on the generic
completed Fock space: retain the amplitude of a configuration exactly when the predicate holds.

This is the indicator-weight specialization of bounded diagonal multiplication. Statistics-specific
layers keep only the predicates and their physical or combinatorial semantics.
-/

namespace SecondQuantization
namespace Common

open Filter Topology
open ContinuousLinearMap

noncomputable section

variable {Config : Type*}

/-- The bounded coordinate projection associated with a predicate on configurations. Its operator
norm is at most one. -/
noncomputable def completedCoordinateProjection (P : Config → Prop) :
    CompletedFock Config →L[ℂ] CompletedFock Config := by
  classical
  exact completedBoundedDiagonalOperator (fun c => if P c then 1 else 0) zero_le_one fun c => by
    by_cases h : P c <;> simp [h]

open scoped Classical in
@[simp]
theorem completedCoordinateProjection_apply (P : Config → Prop)
    (ψ : CompletedFock Config) (c : Config) :
    completedCoordinateProjection P ψ c = if P c then ψ c else 0 := by
  classical
  rw [completedCoordinateProjection, completedBoundedDiagonalOperator_apply]
  by_cases h : P c <;> simp [h]

/-- Coordinate projections are contractive. -/
theorem norm_completedCoordinateProjection_le (P : Config → Prop) (ψ : CompletedFock Config) :
    ‖completedCoordinateProjection P ψ‖ ≤ ‖ψ‖ := by
  classical
  simpa only [completedCoordinateProjection, one_mul] using
    norm_completedBoundedDiagonalOperator_apply_le
      (w := fun c : Config => if P c then 1 else 0) zero_le_one
      (fun c => by by_cases h : P c <;> simp [h]) ψ

/-- Coordinate projections are nonexpansive. -/
theorem dist_completedCoordinateProjection_le (P : Config → Prop)
    (ψ φ : CompletedFock Config) :
    dist (completedCoordinateProjection P ψ) (completedCoordinateProjection P φ) ≤ dist ψ φ := by
  simpa [dist_eq_norm, map_sub] using norm_completedCoordinateProjection_le P (ψ - φ)

open scoped Classical in
/-- A canonical basis state survives a coordinate projection exactly when its configuration
satisfies the predicate. -/
@[simp]
theorem completedCoordinateProjection_basisState (P : Config → Prop)
    (c : Config) :
    completedCoordinateProjection P (completedBasisState c) =
      if P c then completedBasisState c else 0 := by
  classical
  by_cases hc : P c <;> simp [completedCoordinateProjection, hc]


/-- Compressing a summable diagonal series to a coordinate subset keeps exactly the
diagonal terms indexed by that subset. This holds for any configuration predicate,
independently of the origin of the diagonal weights. -/
theorem completedCoordinateProjection_tsum_diagonalTerm
    (P : Config → Prop) (a : Config → ℂ)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config)
    (hA : HasSum
      (fun c : Config =>
        (completedHilbertBasis (Config := Config)).diagonalTerm a c) A) :
    (∑' c : {c : Config // P c},
      (completedHilbertBasis (Config := Config)).diagonalTerm a c.val) =
      (completedCoordinateProjection P).comp
        (A.comp (completedCoordinateProjection P)) := by
  classical
  let b := completedHilbertBasis (Config := Config)
  let Q := completedCoordinateProjection P
  let L : (CompletedFock Config →L[ℂ] CompletedFock Config) →L[ℂ]
      (CompletedFock Config →L[ℂ] CompletedFock Config) :=
    (ContinuousLinearMap.mulLeftRight ℂ
      (CompletedFock Config →L[ℂ] CompletedFock Config)) Q Q
  have hterm (c : Config) :
      L (b.diagonalTerm a c) =
        if P c then b.diagonalTerm a c else 0 := by
    apply ContinuousLinearMap.ext
    intro ψ
    change Q ((b.diagonalTerm a c) (Q ψ)) =
      (if P c then b.diagonalTerm a c else 0) ψ
    simp only [HilbertBasis.diagonalTerm, smul_apply,
      InnerProductSpace.rankOne_apply, map_smul, b, completedHilbertBasis_apply]
    by_cases hc : P c
    · simp [Q, hc, inner_completedBasisState_left,
        completedCoordinateProjection_apply, completedCoordinateProjection_basisState]
    · simp [Q, hc, inner_completedBasisState_left,
        completedCoordinateProjection_apply, completedCoordinateProjection_basisState]
  have hsubset :
      HasSum (fun c : {c : Config // P c} => b.diagonalTerm a c.val) (L A) := by
    apply (hasSum_subtype_iff_indicator).2
    apply (hA.mapL L).congr_fun
    intro c
    rw [hterm]
    by_cases hc : P c <;> simp [Set.indicator, hc]
  have hL : L A = Q.comp (A.comp Q) := by
    apply ContinuousLinearMap.ext
    intro ψ
    change Q (A (Q ψ)) = Q (A (Q ψ))
    rfl
  exact hsubset.tsum_eq.trans hL

/-- A coordinate projection fixes an algebraic vector whenever its mask retains every
configuration in that vector's finite support. -/
theorem completedCoordinateProjection_algebraicToCompleted_of_support
    (P : Config → Prop) (x : AlgebraicFock Config)
    (hP : ∀ c ∈ x.support, P c) :
    completedCoordinateProjection P (algebraicToCompleted x) = algebraicToCompleted x := by
  classical
  ext c
  rw [completedCoordinateProjection_apply]
  by_cases hc : x c = 0
  · simp [algebraicToCompleted_apply, hc]
  · have hpc : P c := hP c (Finsupp.mem_support_iff.mpr hc)
    simp [algebraicToCompleted_apply, hpc]

/-- Coordinate projections converge strongly to the identity along any filter of masks
eventually retaining each fixed configuration. The configuration type and filter index
need not be countable; no finite-rank assumption is made. -/
theorem tendsto_completedCoordinateProjection_of_eventually
    {ι : Type*} (l : Filter ι) (P : ι → Config → Prop)
    (hP : ∀ c : Config, ∀ᶠ i in l, P i c) (ψ : CompletedFock Config) :
    Tendsto (fun i => completedCoordinateProjection (P i) ψ) l (𝓝 ψ) := by
  classical
  have hfinite (s : Finset Config) :
      ∀ᶠ i in l, ∀ c ∈ s, P i c :=
    (Finset.eventually_all s).2 (fun c _ => hP c)
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases algebraicToCompleted_denseRange.exists_dist_lt ψ hhalf with ⟨x, hx⟩
  have hfix :
      ∀ᶠ i in l, completedCoordinateProjection (P i) (algebraicToCompleted x) =
        algebraicToCompleted x := by
    filter_upwards [hfinite x.support] with i hi
    exact completedCoordinateProjection_algebraicToCompleted_of_support (P i) x hi
  filter_upwards [hfix] with i hi
  have hcontract :
      dist (completedCoordinateProjection (P i) ψ)
          (completedCoordinateProjection (P i) (algebraicToCompleted x)) ≤
        dist ψ (algebraicToCompleted x) :=
    dist_completedCoordinateProjection_le (P i) ψ (algebraicToCompleted x)
  calc
    dist (completedCoordinateProjection (P i) ψ) ψ ≤
        dist (completedCoordinateProjection (P i) ψ)
            (completedCoordinateProjection (P i) (algebraicToCompleted x)) +
          dist (completedCoordinateProjection (P i) (algebraicToCompleted x)) ψ :=
      dist_triangle _ _ _
    _ = dist (completedCoordinateProjection (P i) ψ)
          (completedCoordinateProjection (P i) (algebraicToCompleted x)) +
        dist (algebraicToCompleted x) ψ := by rw [hi]
    _ ≤ dist ψ (algebraicToCompleted x) + dist (algebraicToCompleted x) ψ := by
      exact add_le_add hcontract (le_refl _)
    _ = 2 * dist ψ (algebraicToCompleted x) := by
      rw [dist_comm (algebraicToCompleted x) ψ, two_mul]
    _ < ε := by linarith

end
end Common
end SecondQuantization
