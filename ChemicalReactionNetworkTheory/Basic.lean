
/-

# Complete

- definition of chemical reaction network
- define linkage classes
- define mass action kinetics

# Todo

- number of stoich. distinct complexes
- dimension of stoich. subspace
- definition of deficiency
- definition of complex balanced
- definition of weakly reversible
- deficiency zero theorem
- deficiency one theorem

# References

- "Foundations of Chemical Reaction Network Theory" by Martin Feinberg (2019) https://doi.org/10.1007/978-3-030-03858-8

-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Real
-- definition of an abstract chemical reaction network

-- version 1: as a simple digraph
structure CRN where
  specie: Type u
  complex: Set (Multiset specie)
  reaction: Set (complex × complex)

-- version 2: as a nonsimple digraph
structure CRN2 where
  specie: Type u
  complex: Set (Multiset specie)
  reaction: Type v
  reaction_in: reaction → complex
  reaction_out: reaction → complex

-- version 3: as a quiver
structure CRN3 where
  specie: Type u
  complex: Set (Multiset specie)
  reaction: complex → complex → Type v

example (N: CRN): CRN3 := {
  specie := N.specie
  complex := N.complex
  reaction := fun x y => PLift ((x, y) ∈ N.reaction)
}

example (N: CRN2): CRN3 := {
  specie := N.specie
  complex := N.complex
  reaction := fun _ _ => N.reaction
}

-- assign a CRN to its corresponding digraph
example (N: CRN) [Membership (Multiset specie × Multiset specie) (Set (↑N.complex × ↑N.complex))]:
  Digraph (Multiset specie) := {
  Adj := fun x y => (x, y) ∈ N.reaction
}

example (N: CRN) [Membership (↑N.complex × ↑N.complex) (Set (↑N.complex × ↑N.complex))]:
  Digraph (N.complex) := {
  Adj := fun x y => (x, y) ∈ N.reaction
}

example (N: CRN3): Quiver (N.complex) := {
  Hom := N.reaction
}

def CRN_to_SimpleGraph (N: CRN): SimpleGraph N.complex :=
  SimpleGraph.fromRel fun x y => (x, y) ∈ N.reaction

def connected_components (N: CRN): Type :=
  SimpleGraph.ConnectedComponent (CRN_to_SimpleGraph N)

noncomputable def num_connected_components (N: CRN): Nat :=
  Nat.card (connected_components N)

def count_in {N: CRN} [DecidableEq N.specie] (r: N.reaction) (i: N.specie): Nat :=
  Multiset.count i r.val.1

def count_out {N: CRN} [DecidableEq N.specie] (r: N.reaction) (i: N.specie): Nat :=
  Multiset.count i r.val.2

def diff {N: CRN} [DecidableEq N.specie] (r: N.reaction) (i: N.specie): Int :=
  Int.ofNat (count_out r i) - Int.ofNat (count_in r i)

-- mass action kinetics: given a reaction rate vector k, return the function f
-- that generates the ODE dx/dt = f(x) according to mass action kinetics
noncomputable def mass_action_kinetics {N: CRN} [DecidableEq N.specie]
  (k: N.reaction → Real): (N.specie → Real) → (N.specie → Real) :=
  fun x i => tsum fun r => (k r) * (diff r i) * tprod fun j => (x j)^(count_in r i)
