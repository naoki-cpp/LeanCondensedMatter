import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Finite-coordinate casts for ordered-simplex analysis

Small order facts used when transporting ordered-simplex data across propositionally equal finite
coordinate counts.  These are generic analytic infrastructure and do not belong to a particular
diagram presentation.
-/

namespace intervalIntegral

/-- Casting between propositionally equal finite dimensions preserves strict order. -/
theorem strictMono_finCongr {a b : ℕ} (h : a = b) : StrictMono (finCongr h) := by
  subst b
  simpa using (strictMono_id : StrictMono (fun i : Fin a => i))

end intervalIntegral
