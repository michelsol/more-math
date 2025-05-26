import MoreMath.FinsetCombinatorics

open Finset

/-
What is the minimum number of successive swaps of adjacent letters
in the string $$ABCDEF$$ that are needed to change the string to $$FEDCBA?$$
(For example, $$3$$ swaps are required to change $$ABC$$ to $$CBA;$$
one such sequence of swaps is $$ABC\to BAC\to BCA\to CBA.$$)
-/

theorem amc_2024_amc_10a_6
    (X : Set ℕ)
    (hX : X = {
      N : ℕ | ∃
        (string : ℕ → ℕ → ℕ)
        (letter : ℕ → ℕ)
        (_ : StrictMonoOn letter (Icc 1 6))
        (_ : ∀ k ∈ Icc 1 6, string 0 k = letter k)
        (_ : ∀ k ∈ Icc 1 6, string N k = letter (6 + 1 - k)),
          ∀ i ∈ Ico 0 N,
            ∃ j ∈ Ico 1 6,
              ∀ k ∈ Icc 1 6,
                string (i + 1) k = if k = j then string i (j + 1) else if k = j + 1 then string i j else string i k
    })
    : IsLeast X 15 := by
  convert_to IsLeast X (∑ k ∈ Ico 1 6, k) using 1
  generalize 6 = nLetters at *
  constructor
  . rw [hX]
    dsimp
    -- construct string explicitly
    sorry
  . rw [hX]
    dsimp [lowerBounds]
    intro N
    intro ⟨string, letter, hletter, h1, h2, h3⟩
    clear! X
    induction' nLetters with nLetters ih generalizing N string letter
    . sorry
    .
      choose! j h3 h4 using h3
      let I := {i ∈ Ico 0 N | string i (j i) ≠ letter 1 ∧ string i (j i + 1) ≠ letter 1}
      let J := {i ∈ Ico 0 N | string i (j i) = letter 1 ∨ string i (j i + 1) = letter 1}
      let N' := #I
      let F := (λ (i' : ℕ) (f : (y : ℕ) → y < i' → ℕ → ℕ) ↦ match i' with
        | 0 => λ k ↦ string 0 (k + 1)
        | i' + 1 =>
          let i := Nat.nth I.toSet i'
          λ k ↦ if k = j i then f i' (by simp_wf) (j i + 1) else if k = j i + 1 then f i' (by simp_wf) (j i) else f i' (by simp_wf) k
        )
      let string' := Nat.lt_wfRel.wf.fix F
      have h5 k : string' 0 k = string 0 (k + 1) := congrFun (Nat.lt_wfRel.wf.fix_eq F 0) k
      have h6 i' k : string' (i' + 1) k =
          let i := Nat.nth I.toSet i'
          if k = j i then string' i' (j i + 1) else if k = j i + 1 then string' i' (j i) else string' i' k
        := congrFun (Nat.lt_wfRel.wf.fix_eq F (i' + 1)) k
      let letter' k := letter (k + 1)
      specialize @ih N' string' letter'
      specialize ih (by
        sorry)
      specialize ih (by
        intro k hk
        -- dsimp [string', letter']
        -- exact h1 (k + 1) (by simp at hk ⊢; omega))
        sorry)
      specialize ih (by
        sorry)
      specialize ih (by
        intro i' hi'
        let i := Nat.nth I.toSet i'
        use j i
        use by
          sorry
        intro k hk
        exact h6 i' k)
      sorry
