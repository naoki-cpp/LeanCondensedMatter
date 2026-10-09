import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.TMatrix.ScalarImpurity
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.TMatrix.BornDysonLoop

set_option linter.style.header false

/-!
# Massive-Dirac scalar-impurity T-matrix

ScalarImpurity owns the T-matrix algebra and fixed-loop norm/asymptotic estimates for a supplied
Green matrix. BornDysonLoop owns the finite-cutoff continuum realization and its Born self-energy
identification. This package exposes both responsibilities without attaching loop provenance to
arbitrary matrices.
-/
