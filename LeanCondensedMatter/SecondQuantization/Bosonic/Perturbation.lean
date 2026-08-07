import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.GibbsInteractionPicture
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticVertexBound
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticGibbsSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.FirstDysonGibbsSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.FirstDysonGibbsExpectation

set_option linter.style.header false

/-!
# Bosonic perturbation theory

This umbrella exposes the convergence-aware finite-order bosonic perturbation layer.  The public
boundary records the Gibbs-domain closure and sum/integral interchange needed to promote the
arbitrary-configuration Dyson recursion to normalized thermal coefficients.  Interaction-picture
invariance of the free Gibbs numerator supplies the first-order recursive domain-closure slice
directly from summability of the bare interaction.  Quartic matrix coefficients admit a uniform
quadratic particle-number bound, which together with the free Boltzmann moments proves concrete
Gibbs-domain membership for finite quartic interactions.  Their first Dyson coefficients are again
Gibbs-summable, and their normalized Gibbs expectations satisfy the first recursive interval formula
directly because diagonal interaction-picture evolution is constant in imaginary time.
-/
