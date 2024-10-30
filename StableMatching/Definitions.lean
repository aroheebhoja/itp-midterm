import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

-- Definition of stable matching problem:
-- Sets (A : Set α), (B : Set β) of equal size
-- Preference functions pα : (A × B → ℕ), pβ : (A × B → ℕ)
-- Preference functions have to be injective

-- How do I deal with striking people off a pref list?

section
open Function

-- pa : α → β → β → Prop
-- ∀ a ∈ A, IsLinearOrder (p a)
-- pa a b1 b2 vs. (pa a b1) > (pa a b2)

variable
  (A : Finset α)
  (B : Finset β)
  (pa : α → β → ℕ)
  (pb : β → α → ℕ)
  (pa_linear : ∀ a ∈ A, Injective (pa a))
  (pb_linear : ∀ b ∈ B, Injective (pb b))
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

variable
  (M : Finset (α × β))
  (M_partial : M.card < A.card)
  (M_stable : isStableMatching A B pa pb M)

theorem exists_larger : ∃ (M' : Finset (α × β)),
        isStableMatching A B pa pb M' ∧ M'.card = M.card + 1 := by
  -- Choose a ∈ A such that ¬∃ b ∈ B, ((a, b) ∈ M)
  -- a proposes to b, the top person on its pref list who has not yet been proposed to
  -- Case 1: b is unmatched. Then, M' = M ∪ (a, b). Done!
  -- Case 2 (*): ∃ a' ∈ A, ((a', b) ∈ M). Then,
  -- M'' = (M \ (a', b)) ∪ (a, b).
  -- Now, a' proposes to b', the next person on its pref list after b
  -- Case 1: b' is unmatched. Then, M' = M'' ∪ (a', b'), and we're done
  -- Case 2: ∃ a'' ∈ A, ((a'', b') ∈ M). Then, we repeat the above step (*) until we find
  -- an unmatched member of B. We're guaranteed to find such a member
  -- since M is a partial matching and B is a finite set. Done! (how do we formalize this???)
  sorry


end

-- DEFINITIONS --

-- Given an instance of the SMP (A, B, pα, pβ)
-- and a (partial) matching M : A × B

-- (a, b) ∈ M is an *unstable* pair if ∃ (c, d) ∈ M such that:
-- pα (a, d) > pα (a, b)
-- pβ (a, d) > pα (c, d)
-- (That is, a and d prefer each other to their current pairs)

-- A (partial) matching M is *stable* if there are no unstable pairs.

-- THEOREM --

-- Given an instance of the SMP (A, B, pα, pβ)
-- and a *partial* stable matching M : A × B of size k

-- There exists a stable matching M' of size k+1.

-- Probably two cases: someone in set A proposes to an unmatched member of set B (we're done)
-- someone in set A proposes to a matched member of set B (we have a new matching of size k)
-- someone unmatched will get proposed to eventually

-- More stuff --

-- Can apply this argument inductively to prove that there exists a stable
-- matching for every instance of the problem (this is the Gale Shapley algo)

-- Regardless of order of proposals we get the same result
-- (this is not that interesting)

-- Optimality and pessimality depending on which side is proposing
-- Improvement lemma: if a member of proposed set is matched with someone
-- in a partial stable matching, they'll only end up with someone better
-- in a stable matching of increased size

-- Stable roommates problem
