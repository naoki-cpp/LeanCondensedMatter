import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.style.header false

/-!
# Pulling graph walks back through a vertex map

When the image of a vertex map is closed under ambient adjacency and the map reflects adjacency,
every ambient walk starting in the image remains there and yields reachability in the source graph.
-/

namespace SimpleGraph

variable {V W : Type*}

/-- An ambient walk starting in the image of an adjacency-closed map lifts to a reachable source
vertex, provided that adjacency between image vertices reflects to source adjacency. -/
theorem exists_reachable_of_walk_of_adj_closed
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hclosed : ∀ x u, H.Adj (f x) u → ∃ y, u = f y)
    (hreflect : ∀ x y, H.Adj (f x) (f y) → G.Adj x y) :
    ∀ {u v : W}, H.Walk u v →
      ∀ x : V, u = f x → ∃ y, v = f y ∧ G.Reachable x y := by
  intro u v p
  induction p with
  | nil => exact fun x hx => ⟨x, hx, SimpleGraph.Reachable.refl _⟩
  | cons hadj p ih =>
      intro x hx
      subst hx
      obtain ⟨x', hx'⟩ := hclosed x _ hadj
      obtain ⟨y, hy, hreach⟩ := ih x' hx'
      refine ⟨y, hy, SimpleGraph.Reachable.trans ?_ hreach⟩
      exact SimpleGraph.Adj.reachable (hreflect x x' (hx' ▸ hadj))

end SimpleGraph
