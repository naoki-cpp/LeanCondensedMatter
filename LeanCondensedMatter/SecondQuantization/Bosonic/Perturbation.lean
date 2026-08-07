import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.GibbsInteractionPicture

set_option linter.style.header false

/-!
# Bosonic perturbation theory

This umbrella exposes the convergence-aware finite-order bosonic perturbation layer.  The public
boundary records the Gibbs-domain closure and sum/integral interchange needed to promote the
arbitrary-configuration Dyson recursion to normalized thermal coefficients.  Interaction-picture
invariance of the free Gibbs numerator now supplies the first-order recursive domain-closure slice
directly from summability of the bare interaction.
-/
