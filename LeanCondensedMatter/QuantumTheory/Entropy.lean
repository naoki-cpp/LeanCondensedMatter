import LeanCondensedMatter.QuantumTheory.Entropy.Basic
import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal

/-!
# Canonical entropy API

This umbrella module exposes the dimension-independent, `ENNReal`-valued von Neumann entropy and
its diagonal-state formulas. Finite-dimensional entropy is treated through finiteness and `toReal`
specialization theorems, not through a competing state or entropy definition.
-/
