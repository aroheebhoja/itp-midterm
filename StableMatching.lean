-- This module serves as the root of the `StableMatching` library.
-- Import modules here that should be built as part of the library.
import StableMatching.Definitions

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


-- pa : α → β → β → Prop
-- ∀ a ∈ A, IsLinearOrder (p a)
-- pa a b1 b2 vs. (pa a b1) > (pa a b2)
