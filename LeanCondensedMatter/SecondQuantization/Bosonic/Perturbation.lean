import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsSeries
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.GibbsInteractionPicture
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticVertexBound
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticGibbsSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticDysonExpansion

set_option linter.style.header false

/-!
# Bosonic perturbation theory

The convergence-aware finite-order bosonic perturbation layer keeps free-Gibbs summability
explicit on the genuinely infinite occupation space while avoiding any assumed interchange of the
infinite Gibbs sum with the recursive operator-valued Dyson integral.

For finitely supported quartic interactions, the free interaction-picture evolution of each vertex
is a scalar energy-shift factor times the bare vertex operator. This gives a finite vertex-sequence
expansion of every finite-order Dyson coefficient before taking a Gibbs expectation. The downstream
thermal diagrammatic layer proves Gibbs-domain membership for those coefficients at all finite
orders from summability of finite thermal-field products.
-/
