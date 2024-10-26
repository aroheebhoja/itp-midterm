import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

-- Definition of stable matching problem:
-- Sets (A : Set α), (B : Set β) of equal size
-- Preference functions pα : (A × B → ℕ), pβ : (A × B → ℕ)
-- Preference functions have to be injective

-- How do I deal with striking people off a pref list?

structure StableMatchingProblem {α : Type*} {β : Type*} where
  A := Finset α
  B := Finset β
  p₁ := α × β → ℕ
  p₂ := α × β → ℕ
  p₁_injective := sorry
  p₂_injective := sorry
  same_size := sorry -- A and B have same cardinality

structure Matching {α : Type*} [DecidableEq α]
                   {β : Type*} [DecidableEq β] where
  pairs := Finset (α × β)
  a_unique := sorry
  b_unique := sorry
  size := sorry

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
