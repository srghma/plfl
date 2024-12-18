import Aesop
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

-- abbrev X : Type := Fin 2

def ABC = a | b | c

def x : Finset X := Finset.univ

-- def x_permutations : Finset (Finset (Finset X)) := x.powerset.powerset

def my_topology : Finset (Finset X) := {∅, {1}, Finset.univ}

-- Helper lemma to show a set is in my_topology
lemma mem_my_topology (s : Finset X) :
  s ∈ my_topology ↔ s = ∅ ∨ s = {1} ∨ s = Finset.univ := by {
  simp [my_topology]
}

-- Prove it forms a topology
def my_topological_space : TopologicalSpace X := {
  IsOpen := λ s ↦ ∃ t ∈ my_topology, s = t.toSet
  isOpen_univ := by {
    simp [my_topology]
  },
  isOpen_inter := by {
    intros s₁ s₂ h₁ h₂
    simp [mem_my_topology] at *
    cases h₁ with
    | inl h₁ => {
      rw [h₁]
      simp
    }
    | inr h₁ => {
      cases h₁ with
      | inl h₁ => {
        cases h₂ with
        | inl h₂ => {
          rw [h₁, h₂]
          simp
        }
        | inr h₂ => {
          cases h₂ with
          | inl h₂ => {
            rw [h₁, h₂]
            simp
          }
          | inr h₂ => {
            rw [h₁, h₂]
            simp
          }
        }
      }
      | inr h₁ => {
        cases h₂ with
        | inl h₂ => {
          rw [h₁, h₂]
          simp
        }
        | inr h₂ => {
          cases h₂ with
          | inl h₂ => {
            rw [h₁, h₂]
            simp
          }
          | inr h₂ => {
            rw [h₁, h₂]
            simp
          }
        }
      }
    }
  },
  isOpen_sUnion := by {
    intros S hS
    by_cases h : S = ∅
    · use ∅
      constructor
      · simp [my_topology]
      · rw [h]
        simp
    sorry
  }
}
