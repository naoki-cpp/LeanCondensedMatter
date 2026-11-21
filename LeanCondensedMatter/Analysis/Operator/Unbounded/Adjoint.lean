import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option linter.style.header false

/-!
# Double adjoints of unbounded operators

A closed, densely defined operator on a complex Hilbert space has densely defined
adjoint and agrees with its double adjoint. The argument uses orthogonal complements
of operator graphs and does not depend on a particular quantum-mechanical realization.
-/

open Set WithLp

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A closed linear subspace of the product Hilbert space equals its double graph-adjoint. -/
private theorem Submodule.adjoint_adjoint_eq_of_isClosed
    (g : Submodule ℂ (H × H)) (hg : IsClosed (g : Set (H × H))) :
    g.adjoint.adjoint = g := by
  let gw : Submodule ℂ (WithLp 2 (H × H)) :=
    g.comap (WithLp.linearEquiv 2 ℂ (H × H)).toLinearMap
  have hchar (u v : H) :
      (u, v) ∈ g.adjoint ↔ toLp 2 (-v, u) ∈ gwᗮ := by
    rw [Submodule.mem_adjoint_iff, Submodule.mem_orthogonal]
    constructor
    · intro h w hw
      have hwg : (ofLp w : H × H) ∈ g := hw
      have hh := h (ofLp w).1 (ofLp w).2 hwg
      change inner ℂ (ofLp w).1 (-v) + inner ℂ (ofLp w).2 u = 0
      simpa only [inner_neg_right, sub_eq_add_neg, add_comm] using hh
    · intro h a b hab
      have hw : toLp 2 (a, b) ∈ gw := hab
      have hh := h (toLp 2 (a, b)) hw
      change inner ℂ a (-v) + inner ℂ b u = 0 at hh
      simpa only [inner_neg_right, sub_eq_add_neg, add_comm] using hh
  have hdouble (z : H × H) :
      z ∈ g.adjoint.adjoint ↔ toLp 2 z ∈ gwᗮᗮ := by
    rw [Submodule.mem_adjoint_iff, Submodule.mem_orthogonal]
    constructor
    · intro h w hw
      let q : H × H := ((ofLp w).2, -(ofLp w).1)
      have hq : q ∈ g.adjoint := (hchar q.1 q.2).2 (by
        change toLp 2 (-(-(ofLp w).1), (ofLp w).2) ∈ gwᗮ
        simpa only [neg_neg, toLp_ofLp] using hw)
      have hh := h q.1 q.2 hq
      change inner ℂ (ofLp w).1 z.1 + inner ℂ (ofLp w).2 z.2 = 0
      simpa only [q, inner_neg_left, sub_eq_add_neg, add_comm, neg_add_rev, neg_neg] using
        congrArg Neg.neg hh
    · intro h u v huv
      have hw := (hchar u v).1 huv
      have hh := h (toLp 2 (-v, u)) hw
      change inner ℂ (-v) z.1 + inner ℂ u z.2 = 0 at hh
      simpa only [inner_neg_left, sub_eq_add_neg, neg_add_rev, neg_neg] using
        congrArg Neg.neg hh
  have hclosedW : IsClosed (gw : Set (WithLp 2 (H × H))) := by
    exact hg.preimage (WithLp.prod_continuous_ofLp 2 H H)
  have hperp : gwᗮᗮ = gw := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact hclosedW.submodule_topologicalClosure_eq
  ext z
  rw [hdouble, hperp]
  rfl

namespace LinearPMap

variable (A : H →ₗ.[ℂ] H)

/-- The adjoint of a densely defined closed operator is densely defined. -/
theorem adjoint_denseDomain_of_isClosed
    (hDense : Dense (A.domain : Set H)) (hClosed : A.IsClosed) :
    Dense (A.adjoint.domain : Set H) := by
  have hgraph : A.graph.adjoint.adjoint = A.graph :=
    Submodule.adjoint_adjoint_eq_of_isClosed A.graph hClosed
  have hbot : (A.adjoint.domain : Submodule ℂ H)ᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy0 : (0, y) ∈ A.graph.adjoint.adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro u v huv
      have hmem : (u, v) ∈ A.adjoint.graph := by
        simpa only [A.adjoint_graph_eq_graph_adjoint hDense] using huv
      obtain ⟨q, hq⟩ := (A.adjoint.mem_graph_iff').1 hmem
      have hqu : (q : H) = u := congrArg Prod.fst hq
      have horth : inner ℂ u y = 0 := by
        rw [← hqu]
        exact (A.adjoint.domain.mem_orthogonal y).1 hy q q.property
      simpa using horth
    rw [hgraph] at hy0
    obtain ⟨q, hq⟩ := A.mem_graph_iff'.1 hy0
    have hq0 : (q : H) = 0 := congrArg Prod.fst hq
    have hqy : A q = y := congrArg Prod.snd hq
    have hqzero : q = 0 := Subtype.ext hq0
    rw [hqzero] at hqy
    simp only [map_zero] at hqy
    exact hqy.symm
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
  rw [(Submodule.topologicalClosure_eq_top_iff).2 hbot]
  rfl

/-- A densely defined closed operator equals its double adjoint. -/
theorem adjoint_adjoint_eq_of_isClosed
    (hDense : Dense (A.domain : Set H)) (hClosed : A.IsClosed) :
    A.adjoint.adjoint = A := by
  have hAdjDense := A.adjoint_denseDomain_of_isClosed hDense hClosed
  apply LinearPMap.eq_of_eq_graph
  calc
    A.adjoint.adjoint.graph = A.graph.adjoint.adjoint := by
      rw [A.adjoint.adjoint_graph_eq_graph_adjoint hAdjDense,
        A.adjoint_graph_eq_graph_adjoint hDense]
    _ = A.graph := Submodule.adjoint_adjoint_eq_of_isClosed A.graph hClosed

end LinearPMap
