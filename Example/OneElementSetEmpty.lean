import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Aesop

-- Define our three-point space
inductive A : Type
| a : A

-- Define our proposed collection of sets
def τ : Set (Set A) :=
  {∅}

-- Define helper definition for A
def A_univ : Set A := {A.a}


def proposed_top : TopologicalSpace A where
  IsOpen := λ s => s ∈ τ
  isOpen_univ := by
    simp [τ]
    sorry
  isOpen_inter := by
    intro s t hs ht
    simp [τ] at *
    aesop

  isOpen_sUnion := by
    intro S hS
    simp [τ] at *
    by_cases h : ∃ s ∈ S, s = A_univ
    · aesop
    · have hcontr : ∀ s ∈ S, s ≠ A_univ := by
        intro s hs hs'
        exact h ⟨s, hs, hs'⟩
      aesop
-- Theorem that states that there is no topology here
theorem not_topology : ¬ (Nonempty (TopologicalSpace A)) := by
  intro h
  sorry
#print axioms not_topology
