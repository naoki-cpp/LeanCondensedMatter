import LeanCondensedMatter.Transport.FiniteDisorder
import LeanCondensedMatter.Transport.FiniteDisorderResolvent
import LeanCondensedMatter.Transport.FiniteDisorderMoments
import LeanCondensedMatter.Transport.FiniteDisorderBorn
import LeanCondensedMatter.Transport.FiniteDisorderAdvancedBorn
import LeanCondensedMatter.Transport.FiniteDisorderSCBA

set_option linter.style.header false

/-!
# Finite disorder transport API

Public umbrella for exact finite disorder ensembles, disorder resolvents and moments, and the
Born/advanced-Born/SCBA approximation layers. Exact averaging and approximation data remain
logically distinct.

Vertex ladders and concrete disorder models are downstream additions.
-/
