import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Finset

variable {α : Type*} [Inhabited α]

-- Code for argmax function and spec from here:
-- https://piazza.com/class/m01h6rlmn3z6vd/post/88
noncomputable def argmax (f : α → ℤ) (s : Finset α) : α :=
  if h : s.Nonempty then
    have h' : (s.image f).Nonempty := by
      rw [image_nonempty]; exact h
    have : (s.image f).max' h' ∈ s.image f := by
      exact max'_mem (image f s) h'
    have : ∃ a ∈ s, f a = (s.image f).max' h' := by
      simpa using this
    Classical.choose this
  else
    default

theorem argmax_spec (s : Finset α) (f : α → ℤ) (h : s.Nonempty) :
    s.argmax f ∈ s ∧ ∀ x ∈ s, f x ≤ f (s.argmax f) := by
  have h' : (s.image f).Nonempty := by
    rw [image_nonempty]; exact h
  have : (s.image f).max' h' ∈ s.image f := by
    exact max'_mem (image f s) h'
  have : ∃ a ∈ s, f a = (s.image f).max' h' := by
    simpa using this
  have : s.argmax f ∈ s ∧ f (s.argmax f) = (s.image f).max' h' := by
    rw [argmax, dif_pos h]; dsimp
    apply Classical.choose_spec this
  use this.1
  rw [this.2]
  intro x hx
  apply le_max' _ _ (mem_image_of_mem f hx)

section
open Function
open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
[Inhabited α] [Inhabited β]

  (pa : α → β → ℤ)
  (pb : β → α → ℤ)
  (pa_pos : ∀ a, ∀ b, pa a b > 0)
  (pb_pos : ∀ b, ∀ a, pb b a > 0)
  (pa_linear : ∀ a, Injective (pa a))
  (pb_linear : ∀ b, Injective (pb b))
  (A_B_same_size : Fintype.card α = Fintype.card β)

def isMatching (X : Finset (α × β)) :=
  (∀ a, ∀ b₁, ∀ b₂, (a, b₁) ∈ X ∧ (a, b₂) ∈ X → b₁ = b₂) ∧
  (∀ a₁, ∀ b, ∀ a₂, (a₁, b) ∈ X ∧ (a₂, b) ∈ X → a₁ = a₂)

instance : DecidablePred (isMatching (α := α) (β := β)) := by
  unfold isMatching
  infer_instance

def IsUnstablePair x y (X : Finset (α × β)) :=
  (x, y) ∉ X ∧ ∃ a' b', (x, b') ∈ X ∧ (a', y) ∈ X ∧ pa x y > pa x b' ∧ pb y x > pb y a'

instance (x : α) {y : β} {X : Finset (α × β )} : Decidable (IsUnstablePair pa pb x y X) := by
  unfold IsUnstablePair
  infer_instance

def isStableMatching (X : Finset (α × β)) := isMatching X ∧
  ∀ a b, ¬IsUnstablePair pa pb a b X

instance : DecidablePred (isStableMatching pa pb) := by
  unfold isStableMatching
  infer_instance

include pa_linear pb_linear
-- Variant score
def V (X : Finset (α × β)) := X.sum (fun (a, b) => pb b a)

variable
  (M : Finset (α × β))
  (M_partial : #M < Fintype.card α ∧ #M < Fintype.card β)
  (M_stable : isStableMatching pa pb M)
  (M_nonempty : M.Nonempty)

def A' : Finset α := Finset.image (Prod.fst) M
def B' : Finset β := Finset.image (Prod.snd) M

variable (X : Finset (α × β))

include M_stable

theorem A'_unique : ∀ a, a ∈ (A' M) → ∃! b, (a, b) ∈ M := by
  rcases M_stable with ⟨⟨h1 , h2⟩, _⟩
  intro a ha
  simp [A'] at ha
  rcases ha with ⟨x, hx⟩
  use x
  aesop

theorem A'_exists : ∀ a, a ∈ (A' M) → ∃ b, (a, b) ∈ M := by
  rcases M_stable with ⟨⟨h1 , h2⟩, _⟩
  intro a ha
  simp [A'] at ha
  rcases ha with ⟨x, hx⟩
  use x

noncomputable def find_pair (a : α) (h : a ∈ (A' M)) :=
  have : ∀ a, a ∈ (A' M) → ∃ b, (a, b) ∈ M := by
    exact fun a b ↦ A'_exists pa pb pa_linear pb_linear M M_stable a b
  (a, Classical.choose (this a h))

theorem find_pair_spec a (h : a ∈ (A' M)) : find_pair pa pb pa_linear pb_linear M M_stable a h ∈ M := by sorry

theorem A'_card : #(A' M) = #M := by
  apply card_bij (find_pair pa pb pa_linear pb_linear M M_stable)
  intro a ha
  simp [find_pair]
  sorry
  have : ∀ a, a ∈ (A' M) → ∃! b, (a, b) ∈ M := by sorry
  intro b hb c hc d
  let (b', x) := (find_pair pa pb pa_linear pb_linear M M_stable) b hb
  let (c', y) := (find_pair pa pb pa_linear pb_linear M M_stable) c hc
  have : b = b' := by sorry
  rcases M_stable with ⟨⟨h1 , h2⟩, _⟩
  sorry
  sorry

noncomputable def choose_next (a : α) : β :=
  let unmatched : Finset β := Finset.univ \ (B' M)
  let preferred : Finset β := {b | ∃ a', (a', b) ∈ M ∧ pb b a > pb b a'}
  let choices := unmatched ∪ preferred
  choices.argmax (pa a)

variable
  (matched_implies_chosen : ∀ (X : Finset (α × β)), isStableMatching pa pb X → ∀ a b, (a, b) ∈ X → b = choose_next pa pb (X \ {(a, b)}) a)

include matched_implies_chosen
theorem M_matched_implies_chosen : ∀ a b, (a, b) ∈ M → b = choose_next pa pb (M \ {(a, b)}) a := by
  exact matched_implies_chosen M M_stable

include M_partial
theorem exists_unmatched_b : ∃ b, b ∉ (B' M) := by
  let B' := B' M
  have hcard : #B' ≤ #M := by
    apply card_image_le
  have hB' : B' ⊂ univ := by
      apply ssubset_univ_iff.mpr
      have : #B' < Fintype.card β := by
        exact Nat.lt_of_le_of_lt hcard M_partial.right
      exact (card_lt_iff_ne_univ B').mp this
  apply exists_of_ssubset at hB'
  rcases hB' with ⟨x, _, hxr⟩
  use x

theorem choose_next_spec : choose_next pa pb M a ∈ Finset.univ \ (B' M) ∨
                      choose_next pa pb M a ∈ {b | ∃ a', (a', b) ∈ M ∧ pb b a > pb b a'} := by
  let b := choose_next pa pb M a
  have b_def : b = choose_next pa pb M a := by rfl
  let unmatched : Finset β := Finset.univ \ (B' M)
  let preferred : Finset β := {b | ∃ a', (a', b) ∈ M ∧ pb b a > pb b a'}
  let choices := (unmatched ∪ preferred)
  have ⟨x, hx⟩ : ∃ b, b ∉ (B' M) := by
    exact exists_unmatched_b pa pb pa_linear pb_linear M M_partial M_stable matched_implies_chosen
  have nonempty : choices.Nonempty := by
    apply Nonempty.inl
    apply nonempty_iff_ne_empty.mpr
    aesop
  have : b = choices.argmax (pa a) := by
    rw [b_def]
    rfl
  rcases argmax_spec (unmatched ∪ preferred) (pa a) nonempty with ⟨left, _⟩
  have : b ∈ (unmatched ∪ preferred) := by
    exact left
  aesop

theorem choose_next_is_argmax : ∀ a, ¬∃ a' b', (a', b') ∈ M ∧ pa a b' > pa a (choose_next pa pb M a) ∧ pb b' a > pb b' a' := by
  rintro a ⟨a', b', h1, h2, h3⟩
  let unmatched : Finset β := Finset.univ \ (B' M)
  let preferred : Finset β := {b | ∃ a', (a', b) ∈ M ∧ pb b a > pb b a'}
  have ha : b' ∈ preferred := by
    simp [preferred]
    use a'
  have hb : b' ∈ unmatched ∪ preferred := by
    simp; right; exact ha
  have nonempty : (unmatched ∪ preferred).Nonempty := by
    apply Nonempty.inr
    apply nonempty_iff_ne_empty.mpr
    exact ne_empty_of_mem ha
  have hd: ∀ y ∈ (unmatched ∪ preferred), pa a y ≤ pa a (choose_next pa pb M a) := by
    exact (argmax_spec (unmatched ∪ preferred) (pa a) nonempty).right
  specialize hd b' hb
  linarith

theorem choose_next_is_argmax' : ∀ a, ¬∃ b, b ∈ (Finset.univ \ (B' M)) ∧ pa a b > pa a (choose_next pa pb M a) := by
  rintro a ⟨b, h1, h2⟩
  let unmatched : Finset β := Finset.univ \ (B' M)
  let preferred : Finset β := {b | ∃ a', (a', b) ∈ M ∧ pb b a > pb b a'}
  have ha : b ∈ unmatched := by
    simp [unmatched]
    exact mem_compl.mp h1
  have hb : b ∈ unmatched ∪ preferred := by
    simp; left; exact ha
  have nonempty : (unmatched ∪ preferred).Nonempty := by
    apply Nonempty.inl
    apply nonempty_iff_ne_empty.mpr
    exact ne_empty_of_mem ha
  have hd: ∀ y ∈ (unmatched ∪ preferred), pa a y ≤ pa a (choose_next pa pb M a) := by
    exact (argmax_spec (unmatched ∪ preferred) (pa a) nonempty).right
  specialize hd b hb
  linarith

include matched_implies_chosen M_stable
theorem all_unmatched_are_worse : ∀ a b b', (a, b) ∈ M ∧ b' ∈ (Finset.univ \ (B' M)) → pa a b > pa a b' := by
  rintro a b b' ⟨h1, h2⟩
  have hb : b = choose_next pa pb (M \ {(a, b)}) a := by exact matched_implies_chosen M M_stable a b h1
  simp [choose_next] at hb
  let unmatched : Finset β := Finset.univ \ (B' (M \ {(a, b)}))
  let preferred : Finset β := {b | ∃ a', (a', b) ∈ (M \ {(a, b)}) ∧ pb b a > pb b a'}
  have preferred_spec : preferred =
        filter (fun b_1 => ∃ a', ((a', b_1) ∈ M ∧ (a' = a → ¬b_1 = b)) ∧ pb b_1 a' < pb b_1 a) univ := by
      ext x
      constructor
      intro hx
      simp [preferred] at hx
      rcases hx with ⟨w, ⟨hw1, hw2⟩, hw3⟩
      simp
      use w
      constructor
      constructor
      exact hw1
      intro h
      exfalso
      contradiction
      exact hw3
      intro hx
      simp [preferred]
      simp at hx
      rcases hx with ⟨w, ⟨hw1, hw2⟩, hw3⟩
      use w
      constructor
      constructor
      exact hw1
      contrapose! hw2
      rw [hw2] at hw1
      rcases M_stable with ⟨⟨M_matching, _⟩, _⟩
      specialize M_matching a x b ⟨hw1, h1⟩
      exact ⟨hw2, M_matching⟩
      exact hw3
  let choices := unmatched ∪ preferred
  have ⟨x, hx⟩ : ∃ b, b ∉ (B' M) := by
    exact exists_unmatched_b pa pb pa_linear pb_linear M M_partial M_stable matched_implies_chosen
  have h3 : B' (M \ {(a, b)}) ⊆ B' M := by
    simp [B']
    apply image_subset_image
    simp
  have h4 : x ∉ B' (M \ {(a, b)}) := by
    contrapose! hx
    apply mem_of_subset h3
    exact hx
  have h5 : x ∈ unmatched := by
    have : x ∈ (M \ {(a, b)}).B' ∨ x ∈ univ \ (M \ {(a, b)}).B' := by
      simp
      exact Decidable.em (x ∈ (M \ {(a, b)}).B')
    rcases this with h | h
    contradiction
    exact h
  have nonempty : (unmatched ∪ preferred).Nonempty := by
    apply Nonempty.inl
    apply nonempty_iff_ne_empty.mpr
    exact ne_empty_of_mem h5
  have h6 : ∀ c ∈ choices, pa a c ≤ pa a (choices.argmax (pa a)) := by
    exact (argmax_spec choices (pa a) nonempty).right
  have h7 : b = choices.argmax (pa a) := by
    rw [hb]
    rw [← preferred_spec]
  have h8 : b' ∈ choices := by
    have : univ \ M.B' ⊆ unmatched := by
      simp [unmatched]
      intro x hx
      simp at hx
      simp
      exact fun a => hx (h3 a)
    have h : b' ∈ unmatched := by
      exact mem_of_subset this h2
    have : unmatched ⊆ choices := by
      exact subset_union_left
    exact mem_of_subset this h
  specialize h6 b' h8
  rw [← h7] at h6
  have : b ≠ b' := by
    have : b ∈ B' M := by
      simp [B']
      use a
    contrapose! this
    rw [this]
    simp at h2
    exact h2
  have : pa a b' ≠ pa a b := by
    contrapose! pa_linear
    use a
    simp [Injective]
    use b, b'
    constructor
    rw [eq_comm] at pa_linear
    exact pa_linear
    exact this
  exact lt_of_le_of_ne h6 this

include M_stable


-- Theorem 1: if there exists a partial stable matching M, we can find a stable matching M'
-- with a higher variant score

include M_partial M_stable

theorem exists_unmatched_A : ∃ a, a ∉ (A' M) := by
  let A' := A' M
  have hcard : #A' ≤ #M := by
    apply card_image_le
  have hA' : A' ⊂ univ := by
      apply ssubset_univ_iff.mpr
      have : #A' < Fintype.card α := by
        exact Nat.lt_of_le_of_lt hcard M_partial.left
      exact (card_lt_iff_ne_univ A').mp this
  apply exists_of_ssubset at hA'
  rcases hA' with ⟨x, _, hxr⟩
  use x

variable (A : Finset ℕ) (b : ℕ)

include pb_pos pa_linear pb_linear matched_implies_chosen
theorem SM1 : ∃ (M' : Finset (α × β)), isStableMatching pa pb M' ∧ V pb M' > V pb M := by
  let B' := B' M
  let A' := A' M
  have ⟨a, ha⟩ : ∃ a, a ∉ A' := by
    exact exists_unmatched_A pa pb pa_linear pb_linear M M_partial M_stable matched_implies_chosen
  let b : β := choose_next pa pb M a
  have h1 : b ∈ B' ∨ b ∉ B' := by
    exact Decidable.em (b ∈ B')
  have A'_def : A' = Finset.image (Prod.fst) M := by rfl
  have B'_def : B' = Finset.image (Prod.snd) M := by rfl
  have chooseNextDef : ∀ a, ¬∃ a' b', (a', b') ∈ M ∧ pa a b' > pa a (choose_next pa pb M a) ∧ pb b' a > pb b' a' := by
    exact fun a => choose_next_is_argmax pa pb pa_linear pb_linear M M_partial M_stable matched_implies_chosen a
  rcases h1 with matched | unmatched
  have ⟨a', ha'⟩ : ∃ a', (a', b) ∈ M := by
    rw [B'_def] at matched
    simpa using matched
  have hpref : (pb b a > pb b a') := by
      have : b ∈ Finset.univ \ (B') ∨
          b ∈ {b | ∃ a', (a', b) ∈ M ∧ pb b a > pb b a'} := by
          exact
            choose_next_spec pa pb pa_linear pb_linear M M_partial M_stable matched_implies_chosen
      rcases this with left | right
      · simp at left
        contradiction
      · simp at right
        rcases right with ⟨x, ⟨h1, h2⟩⟩
        have : x = a' := by
          rcases M_stable with ⟨⟨_, right⟩, _⟩
          apply right x b a'
          exact ⟨h1, ha'⟩
        rw [this] at h2
        linarith
  use (M \ {(a', b)}) ∪ {(a, b)}
  constructor
  · constructor
    · constructor
      · intro x y₁ y₂ ⟨h1, h2⟩
        have ha : x = a ∨ x ≠ a := by
          exact eq_or_ne x a
        rcases ha with eq | ne
        have hm : ∀ y, (x, y) ∉ M := by
          rw [eq]
          rw [A'_def] at ha
          simpa using ha
        simp at h1 h2
        rcases h1 with ⟨hm1, _⟩ | ⟨_, h1⟩
        · specialize hm y₁
          contradiction
        · rcases h2 with ⟨hm2, _⟩ | ⟨_, h2⟩
          · specialize hm y₂
            contradiction
          rw [h1, h2]
        have h3 : (x, y₁) ∈ M := by
          simp at h1
          rcases h1 with ⟨left, _⟩ | ⟨right, _⟩
          · exact left
          contradiction
        have h4 : (x, y₂) ∈ M := by
          simp at h2
          rcases h2 with ⟨left, _⟩ | ⟨right, _⟩
          · exact left
          contradiction
        rcases M_stable with ⟨⟨left, _⟩, _⟩
        apply left x y₁ y₂
        exact ⟨h3, h4⟩
      · intro x₁ y x₂ ⟨h1, h2⟩
        have hb : y = b ∨ y ≠ b := by
          exact eq_or_ne y b
        rcases hb with eq | ne
        have h : ∀ x, (x, y) ∈ M → x = a' := by
          intro x hx
          rcases M_stable with ⟨⟨_, hm⟩, _⟩
          apply hm x y a'
          constructor
          exact hx
          rw [eq]
          exact ha'
        simp at h1 h2
        rcases h1 with ⟨hc1, hc2⟩ | ⟨h1, _⟩
        · specialize hc2 (h x₁ hc1)
          contradiction
        · rcases h2 with ⟨hc1, hc2⟩ | ⟨h2, _⟩
          · specialize hc2 (h x₂ hc1)
            contradiction
          rw [h1, h2]
        have h3 : (x₁, y) ∈ M := by
          simp at h1
          rcases h1 with ⟨hc1, _⟩ | ⟨_, _⟩
          · exact hc1
          contradiction
        have h4 : (x₂, y) ∈ M := by
          simp at h2
          rcases h2 with ⟨hc1, _⟩ | ⟨_, _⟩
          · exact hc1
          contradiction
        rcases M_stable with ⟨⟨_, right⟩, _⟩
        apply right x₁ y x₂
        exact ⟨h3, h4⟩
    rcases M_stable with ⟨M_matching, M_stable⟩
    intro x y h
    rcases h with ⟨h1, x', y', h2, h3, hp1, hp2⟩
    simp at h1 h2 h3 hp1 hp2
    simp_all
    rcases h1 with ⟨h11, h12⟩
    have : (x, y) ∈ M ∨ (x, y) ∉ M := by exact Decidable.em ((x, y) ∈ M)
    rcases this with h' | h'
    simp_all
    contrapose! M_matching
    simp [isMatching]
    intro ha
    contrapose! ha
    have : b ≠ y' := by
      contrapose! pb_linear
      exfalso
      rw [pb_linear] at hp1
      linarith
    use a', b, y'
    constructor
    assumption
    constructor
    exact h2.left
    exact this
    contrapose! M_stable
    use x, y
    constructor
    exact h'
    rcases h2 with ⟨h2, _⟩ | h2
    rcases h3 with ⟨h3, _⟩ | h3
    · use x', y'
    simp_all [h3.left, h3.right]
    use a', y'
    constructor
    exact h2
    constructor
    assumption
    constructor
    assumption
    linarith
    simp_all [h2.left, h2.right]
    have c1 : ∃ a' b', (a', b') ∈ M ∧ pa a b' > pa a b ∧ pb b' a > pb b' a' := by
      use x', y
    have c2 : ∀ a, ¬∃ a' b', (a', b') ∈ M ∧ pa a b' > pa a (choose_next pa pb M a) ∧ pb b' a > pb b' a' := by
      aesop
    specialize c2 a
    contradiction
  · have h1 : V pb (M \ {(a', b)} ∪ {(a, b)}) =
             V pb (M \ {(a', b)}) + V pb {(a, b)} := by
      apply sum_union
      simp
      rcases M_stable with ⟨⟨_, right⟩, _⟩
      specialize right a b a'
      intro ha
      exact right ⟨ha, ha'⟩
    have : {(a', b)} ⊆ M := by
      exact singleton_subset_iff.mpr ha'
    have h2 : V pb (M \ {(a', b)}) =
            V pb M - V pb {(a', b)} := by
        apply sum_sdiff_eq_sub
        exact this
    rw [h1, h2]
    have : V pb {(a, b)} = pb b a := by
      apply sum_singleton
    rw [this]
    have : V pb {(a', b)} = pb b a' := by
      apply sum_singleton
    rw [this]
    simp
    have : pb b a - pb b a' > 0 := by linarith
    have h : V pb M < V pb M + (pb b a - pb b a') := by
      exact Int.lt_add_of_pos_right (V pb M) this
    have : V pb M - pb b a' + pb b a = V pb M + (pb b a - pb b a') := by
      exact add_comm_sub (V pb M) (pb b a') (pb b a)
    rw [← this] at h
    exact h
  use M ∪ {(a, b)}
  constructor
  · constructor
    · constructor
      · intro x y₁ y₂ ⟨h1, h2⟩
        have ha : x = a ∨ x ≠ a := by
          exact eq_or_ne x a
        rcases ha with eq | ne
        have hm : ∀ y, (x, y) ∉ M := by
          rw [eq]
          rw [A'_def] at ha
          simpa using ha
        simp at h1 h2
        rcases h1 with _ | ⟨_, h1⟩
        · specialize hm y₁
          contradiction
        · rcases h2 with _ | ⟨_, h2⟩
          · specialize hm y₂
            contradiction
          rw [h1, h2]
        have h3 : (x, y₁) ∈ M := by
          simp at h1
          rcases h1 with left | ⟨right, _⟩
          · exact left
          contradiction
        have h4 : (x, y₂) ∈ M := by
          simp at h2
          rcases h2 with left | ⟨right, _⟩
          · exact left
          contradiction
        rcases M_stable with ⟨⟨left, _⟩, _⟩
        apply left x y₁ y₂
        exact ⟨h3, h4⟩
      · intro x₁ y x₂ ⟨h1, h2⟩
        have hb : y = b ∨ y ≠ b := by
          exact eq_or_ne y b
        rcases hb with eq | ne
        have hm : ∀ x, (x, y) ∉ M := by
          rw [eq]
          rw [B'_def] at unmatched
          simpa using unmatched
        simp at h1 h2
        rcases h1 with _ | ⟨h1, _⟩
        · specialize hm x₁
          contradiction
        · rcases h2 with _ | ⟨h2, _⟩
          · specialize hm x₂
            contradiction
          rw [h1, h2]
        have h3 : (x₁, y) ∈ M := by
          simp at h1
          rcases h1 with left | ⟨_, _⟩
          · exact left
          contradiction
        have h4 : (x₂, y) ∈ M := by
          simp at h2
          rcases h2 with left | ⟨_, _⟩
          · exact left
          contradiction
        rcases M_stable with ⟨⟨_, right⟩, _⟩
        apply right x₁ y x₂
        exact ⟨h3, h4⟩
    rcases M_stable with ⟨M_matching, M_stable⟩
    intro x y h
    rcases h with ⟨h1, x', y', h2, h3, hp1, hp2⟩
    simp at hp1 hp2 h1 h2 h3
    rcases h2 with h2 | ⟨h21, h22⟩
    · rcases h3 with h3 | ⟨h31, h32⟩
      · contrapose! M_stable
        use x, y
        constructor
        exact h1.left
        use x', y'
      · rw [h32] at hp1
        rw [h31] at hp2
        have h : pa x y' > pa x b := by
          apply all_unmatched_are_worse pa pb pa_linear pb_linear M M_partial ⟨M_matching, M_stable⟩ matched_implies_chosen x y' b
          constructor
          exact h2
          simp
          exact unmatched
        linarith
    · simp [h21, h22] at hp1 hp2 h1 h3
      rcases h3 with h3 | ⟨h31, h32⟩

      have : ∃ a' b', (a', b') ∈ M ∧ pa a b' > pa a b ∧ pb b' a > pb b' a' := by
        use x', y
      have h : ∀ a, ¬∃ a' b', (a', b') ∈ M ∧ pa a b' > pa a (choose_next pa pb M a) ∧ pb b' a > pb b' a' := by
        exact fun a ↦ chooseNextDef a
      specialize h a
      contradiction
      simp [h31, h32] at hp1 hp2 h1
  · have h1 : V pb (M ∪ {(a, b)}) =
             V pb M + V pb {(a, b)} := by
      apply sum_union
      simp
      contrapose! ha
      rw [A'_def]
      apply mem_image.mpr
      use (a, b)
    rw [h1]
    apply Int.lt_add_of_pos_right (V pb M)
    have : V pb {(a, b)} = pb b a := by
      apply sum_singleton
    rw [this]
    specialize pb_pos b a
    assumption

include A_B_same_size
theorem SM2 : ∃ M', isStableMatching pa pb M' ∧ #M' = Fintype.card α := by
  -- set of all stable matchings over A and B
  let S : Finset (Finset (α × β)) := {X : Finset (α × β) | isStableMatching pa pb X}
  have h1 : ∀ s ∈ S, isStableMatching pa pb s := by aesop
  -- argue that the empty matching is trivially in S
  have h2 : S.Nonempty := by
    have : ∅ ∈ S := by
      simp [S]
      constructor; constructor
      simp; simp
      simp [IsUnstablePair]
    apply nonempty_iff_ne_empty.mpr
    exact ne_empty_of_mem this
  let X := argmax (V pb) S
  rcases argmax_spec S (V pb) h2 with ⟨h3, h4⟩
  specialize h1 X h3
  -- Contradiction proof: otherwise we'd have a matching with a higher variant score
  have h8 : #X ≤ Fintype.card α := by
    have ha : #(A' X) = #X := by exact A'_card pa pb pa_linear pb_linear X h1
    have hb : #(A' X) ≤ Fintype.card α := by exact card_le_univ X.A'
    linarith
  have h9 : #X = Fintype.card α := by
    contrapose! h4
    have h10 : #X < Fintype.card α := by exact Nat.lt_of_le_of_ne h8 h4
    have h11 : #X < Fintype.card β := by linarith
    have ⟨M', h5, h6⟩ : ∃ M', isStableMatching pa pb M' ∧ V pb M' > V pb X := by
      apply SM1 pa pb pb_pos pa_linear pb_linear X ⟨h10, h11⟩ h1 matched_implies_chosen
    use M'
    constructor
    simp [S]; exact h5; exact h6
  use X
end
