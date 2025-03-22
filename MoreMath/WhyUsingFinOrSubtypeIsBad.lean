import Mathlib

open Finset

-- Examples where using Fin / Subtype makes proofs harder

example (n : ℕ) (x : ℕ → ℕ) (hx : ∀ k ∈ Icc 0 n, x k = k) :
    2 * ∑ k ∈ Icc 0 n, x k = n * (n + 1) := by
  induction' n with n ih
  . simp [hx 0 (by simp)]
  -- Proof is easy
  . rw [sum_Icc_succ_top (by omega), mul_add]
    specialize ih (by intro k hk; apply hx; simp at hk ⊢; omega)
    rw [ih]
    rw [hx (n + 1) (by simp)]
    ring

example (n : ℕ) (x : Fin (n + 1) → ℕ) (hx : ∀ k, x k = k.val) :
    2 * ∑ k ∈ Icc 0 n, x k = n * (n + 1) := by
  induction' n with n ih
  . simp [hx 0]
  . rw [sum_Icc_succ_top (by omega), mul_add]
    specialize ih (λ k ↦ x k) (by intro k; simpa using hx k)
    -- specialize ih (λ ⟨k, hk⟩ ↦ x ⟨k, by omega⟩) (by intro k; simpa using hx k)
    simp at ih
    simp  [ih]
    -- Proof is annoying
    sorry

example (n : ℕ) (x : Icc 0 n → ℕ) (hx : ∀ k, x k = k.val) :
    2 * ∑ k ∈ (Icc 0 n).attach, x k = n * (n + 1) := by
  induction' n with n ih
  . simp
    intro k hk
    simp [hk, hx]
  . -- Proof is annoying
    sorry



example (n : ℕ) : 2 * ∑ k ∈ Icc 0 n, k = n * (n + 1) := by
  induction' n with n ih
  . simp
-- Proof is easy
  . rw [sum_Icc_succ_top (by omega), mul_add]
    rw [ih]
    ring

example (n : ℕ) : 2 * ∑ k : Fin (n + 1), k = n * (n + 1) := by
  induction' n with n ih
  . simp
-- Proof is annoying
  . sorry

example (n : ℕ) : 2 * ∑ k : Icc 0 n, k.val = n * (n + 1) := by
  induction' n with n ih
  . simp
-- Proof is annoying
  . sorry
