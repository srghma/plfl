import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Aesop

-- Define our three-point space
inductive ABC : Type
| a : ABC
| b : ABC
| c : ABC

-- Define our proposed collection of sets
def τ : Set (Set ABC) :=
  {{ABC.a,ABC.b,ABC.c},{ABC.a,ABC.b},{ABC.a},{ABC.b,ABC.c},{ABC.c},∅}

-- Prove that τ is not closed under finite intersections
lemma notInter : ¬(∀ s t : Set ABC, s ∈ τ → t ∈ τ → s ∩ t ∈ τ) := by
  -- Take specific sets from τ
  let s : Set ABC := {ABC.a, ABC.b}
  let t : Set ABC := {ABC.b, ABC.c}
  have hs : s ∈ τ := by simp [τ]
  have ht : t ∈ τ := by simp [τ]
  -- Compute their intersection
  have h_inter : s ∩ t = {ABC.b} := by
    ext x
    simp [s, t]
    constructor
    · aesop
    · intro h
      cases h
      simp [*]
  -- Show {ABC.b} is not in τ
  have h_not_in_τ : {ABC.b} ∉ τ := by
    simp [τ]
    constructor
    · intro h
      have h1 : ¬ (ABC.a ∈ ({ABC.b} : Set ABC)) := by
        simp
      have h2 : ABC.a ∈ ({ABC.a, ABC.b, ABC.c} : Set ABC) := by
        simp [Set.mem_singleton]
      exact h1 (h ▸ h2)
    · constructor
      · intro h
        have h1 : ABC.a ∉ ({ABC.b} : Set ABC) := by simp
        have h2 : ABC.a ∈ ({ABC.a, ABC.b} : Set ABC) := by simp
        exact h1 (h ▸ h2)
      · intro h
        have h1 : ¬(ABC.c ∈ ({ABC.b} : Set ABC)) := by simp
        have h2 : ABC.c ∈ ({ABC.b, ABC.c} : Set ABC) := by simp
        exact h1 (h.symm ▸ h2)
  -- Conclude τ is not closed under finite intersections
  intro h
  have hb := h s t hs ht
  rw [h_inter] at hb
  exact h_not_in_τ hb

def myIsOpen : Set ABC → Prop := λ s ↦ s ∈ τ
def myisOpen_univ : Set ABC → Prop := λ s ↦ s ∈ τ

-- def my := TopologicalSpace ABC where
--   IsOpen := λ s ↦ s ∈ τ
--   isOpen_univ := _
--   isOpen_inter := λ s t hs ht ↦ sorry

-- Prove τ is not a topology
-- theorem not_topology : ¬ () := by
--   apply notInter
