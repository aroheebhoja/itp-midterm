-- Definition of stable matching problem:
-- Sets (A : Set α), (B : Set β) of equal size
-- Preference functions pα : (A × B → ℕ), pβ : (A × B → ℕ)

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
-- and a (partial) stable matching M : A × B of size k

-- There exists a (partial) stable matching M' of size k+1.

-- PROOF --
-- By assumption!
