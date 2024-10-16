
import Mathlib.Data.Multiset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Real.Basic

import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Path

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.Dimension.Basic

-- definition of an abstract chemical reaction network
structure CRN where
  specie: Type u
  complex: Set (Multiset specie)
  reaction: Set (complex × complex)

-- representation of a CRN as a Digraph
def CRN.toDigraph (N: CRN): Digraph (N.complex) := {
  Adj := fun x y => (x, y) ∈ N.reaction
}

-- representation of a CRN as a quiver
-- this is perhaps the most general/easiest to work with definition
def CRN.toQuiver (N: CRN): Quiver (N.complex) := {
  Hom := fun x y => PLift ((x, y) ∈ N.reaction)
}

instance (N: CRN): Quiver (N.complex) := CRN.toQuiver N

-- definition of reversibility
def CRN.reversible (N: CRN): Prop :=
  ∀ x0 x1: N.complex, (x0, x1) ∈ N.reaction → (x1, x0) ∈ N.reaction

-- a path from x to y is a finite sequence of directed reactions
-- starting at x and ending at y
-- this is equivalent to a path in a quiver
def CRN.path {N: CRN} (x y: N.complex): Type :=
  Quiver.Path x y

-- convert a directed graph to a simple graph
def Digraph_to_SimpleGraph {X: Type u} (G: Digraph X): SimpleGraph X := {
  Adj := fun x y => x ≠ y ∧ (G.Adj x y ∨ G.Adj y x)
  loopless := by intro; simp_all
}

-- A connection, aka linkage, from x to y
-- is a path in the underlying undirected graph of N
def CRN.connection {N: CRN} (x y: N.complex): Type :=
  SimpleGraph.Path (Digraph_to_SimpleGraph (CRN.toDigraph N)) x y

-- Complexes x and y are connected if there exists a connection between them
def CRN.connected {N: CRN} (x y: N.complex): Prop :=
  Nonempty (SimpleGraph.Path (Digraph_to_SimpleGraph (CRN.toDigraph N)) x y)

-- A network is weakly reversible if whenever
-- x is connected to y, then y is connected to x.
def CRN.weak_reversible (N: CRN): Prop :=
  ∀ x y: N.complex, CRN.connected x y → CRN.connected y x

/-

-- deprecated

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
-/

-- assign a CRN to its corresponding digraph
example (N: CRN) [Membership (Multiset specie × Multiset specie) (Set (↑N.complex × ↑N.complex))]:
  Digraph (Multiset specie) := {
  Adj := fun x y => (x, y) ∈ N.reaction
}

example (N: CRN) [Membership (↑N.complex × ↑N.complex) (Set (↑N.complex × ↑N.complex))]:
  Digraph (N.complex) := {
  Adj := fun x y => (x, y) ∈ N.reaction
}
/-
example (N: CRN3): Quiver (N.complex) := {
  Hom := N.reaction
}
-/
def CRN_to_SimpleGraph (N: CRN): SimpleGraph N.complex :=
  SimpleGraph.fromRel fun x y => (x, y) ∈ N.reaction

-- the linkage classes of a network
-- are the connected components of the underlying simple graph
def linkage_classes (N: CRN): Type :=
  SimpleGraph.ConnectedComponent (CRN_to_SimpleGraph N)

noncomputable def num_linkage_classes (N: CRN): Nat :=
  Nat.card (linkage_classes N)

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

-- the stoichiometric subspace, represented as a submodule of Z^specie
def stoich_subspace (N: CRN) [DecidableEq N.specie]: Submodule Int (N.specie → Int) :=
  Submodule.span Int (Set.image diff Set.univ)

-- the rank of the stoichiometric subspace
noncomputable def stoich_subspace_dimension (N: CRN) [DecidableEq N.specie]: Nat :=
  Cardinal.toNat (Module.rank Int (stoich_subspace N))

-- definition of deficiency
noncomputable def deficiency (N: CRN) [Finite N.complex] [DecidableEq N.specie]: Int :=
  (Nat.card N.complex) - (num_linkage_classes N) - (stoich_subspace_dimension N)

-- should be able to prove the deficiency is always nonnegative
theorem deficiency_nonneg (N: CRN) [Finite N.complex] [DecidableEq N.specie]: 0 ≤ deficiency N :=
  sorry
