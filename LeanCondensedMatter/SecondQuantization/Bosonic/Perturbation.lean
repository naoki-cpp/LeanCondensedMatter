import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.GibbsInteractionPicture
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticVertexBound
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.QuarticGibbsSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.FirstDysonGibbsSummable
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.FirstDysonGibbsExpectation

set_option linter.style.header false

/-!
# Bosonic perturbation theory

The convergence-aware finite-order bosonic perturbation layer records the Gibbs-domain closure and
sum/integral interchange needed to turn the algebraic Dyson recursion into normalized thermal
coefficients.

For first order, invariance of diagonal free-Gibbs matrix coefficients under interaction-picture
conjugation reduces Gibbs summability to summability of the bare interaction. Finite quartic
interactions satisfy a uniform quadratic particle-number bound, so free Boltzmann moments imply the
required Gibbs-domain membership. Their first Dyson coefficients are therefore Gibbs-summable, and
their normalized Gibbs expectations satisfy the corresponding interval recursion.
-/
