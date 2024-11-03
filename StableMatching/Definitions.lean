import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

section
open Function
open Finset

variable
  (A : Finset α)
  (B : Finset β)
  (pa : α → β → ℕ)
  (pb : β → α → ℕ)
  (pa' : α → ℕ → β)
  (pb' : β → ℕ → α)
  (pa_linear : ∀ a ∈ A, Injective (pa a))
  (pb_linear : ∀ b ∈ B, Injective (pb b))
  (pa_eq_pa' : ∀ a ∈ A, ∀ b ∈ B, pa' a (pa a b) = b)
  (pb_eq_pb' : ∀ a ∈ A, ∀ b ∈ B, pb' b (pb b a) = a)
  (A_B_same_size : A.card = B.card)

-- X is a subset of the cartesian product of A and B
-- no throuples, no polycules, no infidelity
def isMatching (X : Finset (α × β)) :=
  X ⊆ (A ×ˢ B) ∧
  (∀ a ∈ A, ∀ b₁ ∈ B, (a, b₁) ∈ X → ¬∃ b₂ ∈ B, (a, b₂) ∈ X) ∧
  (∀ a₁ ∈ A, ∀ b ∈ B, (a₁, b) ∈ X → ¬∃ a₂ ∈ A, (a₂, b) ∈ X)

def UnstablePair (X : Finset (α × β)) (a : α) (b : β) :=
  ∃ (c : α) (d : β), ((c, d) ∈ X) ∧ (pa a d > pa a b) ∧ (pb d a > pb d c)

def isStableMatching (X : Finset (α × β)) := isMatching A B X ∧
  ¬∃ (a : α) (b : β), ((a, b) ∈ X) ∧ (UnstablePair pa pb X a b)

-- Variant score: sum over all b in the matching of how much they prefer their current partner
-- by improvement lemma, this has to increase at each iteration of the algorithm
def V (X : Finset (α × β)) := X.sum (fun (a, b) => pb b a)

variable
  (M : Finset (α × β))
  (M_partial : M.card < A.card)
  (M_stable : isStableMatching A B pa pb M)
  (A' : Finset α)
  (B' : Finset β)
  (A'_def : A' ⊂ A ∧ (x ∈ A' → ∃ b ∈ B', (x, b) ∈ M))
  (B'_def : B' ⊂ B ∧ (y ∈ B' → ∃ a ∈ A', (a, y) ∈ M))

include A'_def
theorem can_choose : ∃ a ∈ A, a ∉ A' := by
  apply exists_of_ssubset
  exact A'_def.left

def choose_next' (a : α) (n : ℕ) :=
  let b := pa' a n
  if (∃ x ∈ A, (x, b) ∈ M) then -- if a is already matched to someone
    (if pb b a > pb b x then b else choose_next' a (n + 1))
    else b

def choose_next (a : α) := choose_next' a 0

-- Theorem 1: if there exists a partial stable matching M, we can find a stable matching M'
-- with a higher variant score
theorem SM1 : ∃ (M' : Finset (α × β)), V pb M' > V pb M := by
  sorry


-- Theorem 2: a stable matching with a variant score (___) implies totality
theorem SM2 (X : Finset (α × β)) : V pb X = 15 → X.card = A.card := by
  sorry


-- Theorem 3: can apply theorem 1 inductively to prove that for every instance
-- of the SMP there exists a total stable matching ..


end
