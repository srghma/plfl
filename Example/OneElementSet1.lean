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
  {{A.a}, ∅}
variable (p q r : Prop)

-- theorem t1 : p → q → p := fun hp : p => fun _hq : q => hp
theorem t1 : p → q → p :=
  fun hp : p =>
  fun _hq : q =>
  show p from hp

#print t1

def proposed_top : TopologicalSpace A where
  IsOpen := λ s => s ∈ τ
  isOpen_univ := by
    -- Need to show that the universal set is in τ
    -- But in this case, need to show univ = {A.a} or A is empty
    left
    aesop
  isOpen_inter := by
    intro s t hs ht
    simp [τ] at *
    aesop

  isOpen_sUnion := by
    intro S hS
    simp [τ] at *
    by_cases h : ∃ s ∈ S, s = {A.a}
    · aesop
    · have hcontr : ∀ s ∈ S, s ≠ {A.a} := by
        intro s hs hs'
        exact h ⟨s, hs, hs'⟩
      aesop
