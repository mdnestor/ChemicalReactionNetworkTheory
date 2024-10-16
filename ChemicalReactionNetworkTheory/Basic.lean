
/-

# Complete

- definition of chemical reaction network
- definition of reversibility and weak reversibility
- define linkage classes
- define mass action kinetics

# Todo

- number of stoich. distinct complexes
- dimension of stoich. subspace
- definition of deficiency
- definition of complex balanced
- deficiency zero theorem
- deficiency one theorem

# References

- "Foundations of Chemical Reaction Network Theory" by Martin Feinberg (2019) https://doi.org/10.1007/978-3-030-03858-8

-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.Dimension.Basic

-- definition of an abstract chemical reaction network

-- version 1: as a simple digraph
structure CRN where
  specie: Type u
  complex: Set (Multiset specie)
  reaction: Set (complex × complex)

def CRN.toDigraph (N: CRN): Digraph (N.complex) := {
  Adj := fun x y => (x, y) ∈ N.reaction
}

def CRN.toQuiver (N: CRN): Quiver (N.complex) := {
  Hom := fun x y => PLift ((x, y) ∈ N.reaction)
}

instance (N: CRN): Quiver (N.complex) := CRN.toQuiver N

def CRN.reversible (N: CRN): Prop :=
  ∀ x0 x1: N.complex, (x0, x1) ∈ N.reaction → (x1, x0) ∈ N.reaction

-- definition of a path from x to y
def CRN.path {N: CRN} (x y: N.complex): Type :=
  Quiver.Path x y

-- convert a directed graph to a simple graph
def Digraph_to_SimpleGraph {X: Type u} (G: Digraph X): SimpleGraph X := {
  Adj := fun x y => x ≠ y ∧ (G.Adj x y ∨ G.Adj y x)
  loopless := by intro; simp_all
}

def CRN.connection {N: CRN} (x y: N.complex): Type :=
  SimpleGraph.Path (Digraph_to_SimpleGraph (CRN.toDigraph N)) x y

def CRN.connected {N: CRN} (x y: N.complex): Prop :=
  Nonempty (SimpleGraph.Path (Digraph_to_SimpleGraph (CRN.toDigraph N)) x y)

-- definition of weak reversibility
def CRN.weak_reversible (N: CRN): Prop :=
  ∀ x y: N.complex, CRN.connected x y → CRN.connected y x


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
  fun x i => tsum fun r => (k r) * (diff r i) * tprod fun j => (x j)^(count_in r j)

-- the stoichiometric subspace
def stoich_subspace (N: CRN) [DecidableEq N.specie]: Submodule Int (N.specie → Int) :=
  Submodule.span Int (Set.image diff Set.univ)

noncomputable def stoich_subspace_dimension (N: CRN) [DecidableEq N.specie]: Nat :=
  Cardinal.toNat (Module.rank Int (stoich_subspace N))

noncomputable def deficiency (N: CRN) [DecidableEq N.specie]: Nat :=
  (Nat.card N.complex) - (num_connected_components N) - (stoich_subspace_dimension N)
