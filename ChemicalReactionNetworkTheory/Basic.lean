
import Mathlib.Data.Multiset.Basic

-- definition of an abstract chemical reaction network
structure CRN where
  specie: Type
  complex: Set (Multiset specie)
  reaction: Set (complex × complex)

inductive Path (N: CRN): complex → complex → Type
| nil (x: N.complex): Path N x x
| cons {x: N.complex} {r: N.reaction} (p: Path N x r.val.1): Path N x r.val.2

def exists_path {N: CRN} (x0 x1: N.complex): Prop :=
  Nonempty (Path N x0 x1)

theorem exists_path_refl {N: CRN} (x: N.complex): exists_path x x := by
  use Path.nil x

theorem exists_path_trans {N: CRN} {x y z: N.complex}
  (h1: exists_path x y) (h2: exists_path y z):
  exists_path x z := by
  sorry

def connected {N: CRN} (x0 x1: N.complex): Prop :=
  exists_path x0 x1 ∨ exists_path x1 x0

-- prove `connected` is an equivalence relation
def connected_refl {N: CRN} (x: N.complex): connected x x := by
  apply Or.inl
  exact exists_path_refl x

def connected_symm {N: CRN} {x y: N.complex} (h: connected x y): connected y x := by
  cases h with
  | inl =>
    apply Or.inr
    simp_all
  | inr =>
    apply Or.inl
    simp_all

def connected_trans {N: CRN} {x y z: N.complex} (h1: connected x y) (h2: connected y z): connected x z := by
  sorry

/-

TODO:

- mass action kinetics
- number of stoich. distinct complexes
- number of linkage classes
  - idea; take the quotient of the complexes by the connected relation
- dimension of stoich. subspace
- definition of deficiency
- definition of complex balanced
- definition of weakly reversible
- deficiency zero theorem
- deficiency one theorem

-/
