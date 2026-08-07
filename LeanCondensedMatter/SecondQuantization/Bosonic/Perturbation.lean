import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.GibbsInteractionPicture
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticVertexBound

set_option linter.style.header false

/-!
# Bosonic perturbation theory

This umbrella exposes the convergence-aware finite-order bosonic perturbation layer.  The public
boundary records the Gibbs-domain closure and sum/integral interchange needed to promote the
arbitrary-configuration Dyson recursion to normalized thermal coefficients.  Interaction-picture
invariance of the free Gibbs numerator supplies the first-order recursive domain-closure slice
directly from summability of the bare interaction, while the quartic-vertex bound supplies the
uniform quadratic estimate used to prove concrete Gibbs summability.
-/
