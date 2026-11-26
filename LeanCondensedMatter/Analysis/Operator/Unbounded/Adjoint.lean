import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option linter.style.header false

/-!
# Double adjoints of unbounded operators

A closed, densely defined operator between real or complex Hilbert spaces has densely defined
adjoint and agrees with its double adjoint. The argument uses orthogonal complements
of operator graphs and does not depend on a particular quantum-mechanical realization.
-/

open Set WithLp

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A closed linear subspace of the product Hilbert space equals its double graph-adjoint. -/
private theorem Submodule.adjoint_adjoint_eq_of_isClosed
    (g : Submodule 𝕜 (E × F)) (hg : IsClosed (g : Set (E × F))) :
    g.adjoint.adjoint = g := by
  let gw : Submodule 𝕜 (WithLp 2 (E × F)) :=
    g.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  have hchar (u : F) (v : E) :
      (u, v) ∈ g.adjoint ↔ toLp 2 (-v, u) ∈ gwᗮ := by
    rw [Submodule.mem_adjoint_iff, Submodule.mem_orthogonal]
    constructor
    · intro h w hw
      have hwg : (ofLp w : E × F) ∈ g := hw
      have hh := h (ofLp w).1 (ofLp w).2 hwg
      change inner 𝕜 (ofLp w).1 (-v) + inner 𝕜 (ofLp w).2 u = 0
      simpa only [inner_neg_right, sub_eq_add_neg, add_comm] using hh
    · intro h a b hab
      have hw : toLp 2 (a, b) ∈ gw := hab
      have hh := h (toLp 2 (a, b)) hw
      change inner 𝕜 a (-v) + inner 𝕜 b u = 0 at hh
      simpa only [inner_neg_right, sub_eq_add_neg, add_comm] using hh
  have hdouble (z : E × F) :
      z ∈ g.adjoint.adjoint ↔ toLp 2 z ∈ gwᗮᗮ := by
    rw [Submodule.mem_adjoint_iff, Submodule.mem_orthogonal]
    constructor
    · intro h w hw
      let q : F × E := ((ofLp w).2, -(ofLp w).1)
      have hq : q ∈ g.adjoint := (hchar q.1 q.2).2 (by
        change toLp 2 (-(-(ofLp w).1), (ofLp w).2) ∈ gwᗮ
        simpa only [neg_neg, toLp_ofLp] using hw)
      have hh := h q.1 q.2 hq
      change inner 𝕜 (ofLp w).1 z.1 + inner 𝕜 (ofLp w).2 z.2 = 0
      simpa only [q, inner_neg_left, sub_eq_add_neg, add_comm, neg_add_rev, neg_neg,
        neg_zero] using
        congrArg Neg.neg hh
    · intro h u v huv
      have hw := (hchar u v).1 huv
      have hh := h (toLp 2 (-v, u)) hw
      change inner 𝕜 (-v) z.1 + inner 𝕜 u z.2 = 0 at hh
      simpa only [inner_neg_left, sub_eq_add_neg, neg_add_rev, neg_neg, neg_zero,
        add_comm] using
        congrArg Neg.neg hh
  have hclosedW : IsClosed (gw : Set (WithLp 2 (E × F))) := by
    exact hg.preimage (WithLp.prod_continuous_ofLp 2 E F)
  have hperp : gwᗮᗮ = gw := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact hclosedW.submodule_topologicalClosure_eq
  ext z
  rw [hdouble, hperp]
  rfl

namespace LinearPMap

variable (A : E →ₗ.[𝕜] F)

/-- The adjoint of a densely defined closed operator is densely defined. -/
theorem adjoint_denseDomain_of_isClosed
    (hDense : Dense (A.domain : Set E)) (hClosed : A.IsClosed) :
    Dense (A.adjoint.domain : Set F) := by
  have hgraph : A.graph.adjoint.adjoint = A.graph :=
    Submodule.adjoint_adjoint_eq_of_isClosed A.graph hClosed
  have hbot : (A.adjoint.domain : Submodule 𝕜 F)ᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy0 : (0, y) ∈ A.graph.adjoint.adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro u v huv
      have hmem : (u, v) ∈ A.adjoint.graph := by
        simpa only [A.adjoint_graph_eq_graph_adjoint hDense] using huv
      have horth : inner 𝕜 u y = 0 :=
        (A.adjoint.domain.mem_orthogonal y).1 hy u (LinearPMap.mem_domain_of_mem_graph hmem)
      simpa using horth
    rw [hgraph] at hy0
    obtain ⟨q, hq0, hqy⟩ := A.mem_graph_iff.mp hy0
    have hqzero : q = 0 := Subtype.ext hq0
    simpa [hqzero] using hqy.symm
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
  rw [(Submodule.topologicalClosure_eq_top_iff).2 hbot]
  rfl

/-- A densely defined closed operator equals its double adjoint. -/
theorem adjoint_adjoint_eq_of_isClosed
    (hDense : Dense (A.domain : Set E)) (hClosed : A.IsClosed) :
    A.adjoint.adjoint = A := by
  have hAdjDense := A.adjoint_denseDomain_of_isClosed hDense hClosed
  apply LinearPMap.eq_of_eq_graph
  calc
    A.adjoint.adjoint.graph = A.graph.adjoint.adjoint := by
      rw [A.adjoint.adjoint_graph_eq_graph_adjoint hAdjDense,
        A.adjoint_graph_eq_graph_adjoint hDense]
    _ = A.graph := Submodule.adjoint_adjoint_eq_of_isClosed A.graph hClosed

end LinearPMap

/-! ## Generic self-adjointness criterion -/

namespace LinearPMap

noncomputable section

open Set
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {A : H →ₗ.[𝕜] H}

/-- For a densely defined symmetric partial operator, self-adjointness is equivalent to the reverse
adjoint-domain inclusion. The forward inclusion is already supplied by symmetry. -/
theorem isSelfAdjoint_iff_adjoint_domain_le_of_isFormalAdjoint
    (hdense : Dense ((A.domain : Submodule 𝕜 H) : Set H))
    (hsymm : A.IsFormalAdjoint A) :
    IsSelfAdjoint A ↔ A.adjoint.domain ≤ A.domain := by
  constructor
  · intro hself
    have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hself
    rw [hadj]
  · intro hdom
    rw [LinearPMap.isSelfAdjoint_def]
    have hle : A ≤ A.adjoint := hsymm.le_adjoint hdense
    have hdomain : A.domain = A.adjoint.domain := le_antisymm hle.1 hdom
    exact (LinearPMap.eq_of_le_of_domain_eq hle hdomain).symm

end

end LinearPMap
