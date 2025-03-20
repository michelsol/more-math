import Mathlib

open Finset Classical

-- Functions from a finite set to a finite set

def FunOn {α β : Type _} (s : Set α) (t : Set β) [Inhabited β] :=
  {f : α → β | (∀ x ∈ s, f x ∈ t) ∧ ∀ x ∉ s, f x = default}

noncomputable def FinOn {α : Type _} {β : Type _} (s : Finset α) (t : Finset β) [Inhabited β] :=
  let g : FunOn s t ≃ (s → t) := {
    toFun := λ ⟨f, ⟨hf1, hf2⟩⟩ ↦ λ ⟨x, hx⟩ ↦ ⟨f x, hf1 x hx⟩
    invFun := λ f ↦ ⟨λ x ↦ if hx : x ∈ s then (f ⟨x, hx⟩).1 else default, by
      split_ands; all_goals (intro x hx; simp at hx; simp [hx])⟩
    left_inv := by
      intro ⟨f, hf1, hf2⟩
      ext x
      by_cases hx : x ∈ s
      . simp [hx]
      . simp [hx, hf2 x hx]
    right_inv := by intro f; simp
    }
  letI := g.finite_iff.mpr inferInstance
  letI := Fintype.ofFinite
  (FunOn s.toSet t.toSet).toFinset


theorem card_FinOn {α : Type _} {β : Type _} (s : Finset α) (t : Finset β) [Inhabited β] :
    #(FinOn s t) = #t ^ #s := by
  suffices ∀ n, #s = n → #(FinOn s t) = #t ^ n from this #s rfl
  intro n
  induction' n with n ih generalizing s t
  . intro hs
    replace hs : s = ∅ := by simpa using hs
    suffices ∃ f, FinOn s t = {f} from by simpa [hs, card_eq_one]
    subst hs
    use λ _ ↦ default
    ext f
    suffices (∀ x, f x = default) ↔ f = λ _ ↦ default from by simpa [FinOn, FunOn]
    constructor <;> intro h1
    . ext x; exact h1 x
    . intro x; rw [h1]
  . intro hs
    have h0 : s.Nonempty := by apply nonempty_of_ne_empty; apply_fun (#.); dsimp; omega
    let x0 : α := h0.choose
    have h1 : x0 ∈ s := h0.choose_spec
    let h2 : FinOn s t ≃ (FinOn (s \ {x0}) t) ×ˢ t := {
      toFun := λ ⟨f, hf⟩ ↦ ⟨⟨λ x ↦ if x = x0 then default else f x, f x0⟩, by
        replace hf := by simpa [FinOn, FunOn] using hf
        suffices ((∀ x ∈ s \ {x0}, (if x = x0 then default else f x) ∈ t) ∧ ∀ x ∉ s \ {x0}, ¬x = x0 → f x = default) ∧ f x0 ∈ t from by
          simpa [FinOn, FunOn]
        split_ands
        . intro x hx
          simp at hx
          simp [hx.right, hf.left x hx.left]
        . intro x hx hx2
          simp at hx
          apply hf.right
          intro hx3
          exact hx2 (hx hx3)
        . exact hf.left x0 h1⟩
      invFun := λ ⟨⟨g, y0⟩, h2⟩ =>
        ⟨λ x ↦ if x = x0 then y0 else g x, by
          obtain ⟨⟨h2, h3⟩, h4⟩ := by simpa [FinOn, FunOn] using h2
          suffices (∀ x ∈ s, (if x = x0 then y0 else g x) ∈ t) ∧ ∀ x ∉ s, (if x = x0 then y0 else g x) = default from by simpa [FinOn, FunOn]
          split_ands
          . intro x hx
            by_cases h5 : x = x0
            . simp [h5, h4]
            . suffices g x ∈ t from by simpa [h5]
              exact h2 _ hx h5
          . intro x hx
            have h5 : x ≠ x0 := by intro c1; subst c1; exact hx h1
            simp [h5, h3 x (by simp [hx])]⟩
      left_inv := by
        intro ⟨f, hf⟩
        ext x
        by_cases hx : x = x0 <;> simp [hx]
      right_inv := by
        intro ⟨⟨g, y0⟩, hg⟩
        obtain ⟨⟨h2, h3⟩, h4⟩ := by simpa [FinOn, FunOn] using hg
        ext x
        . by_cases hx : x = x0
          . simp [hx, h3 x0 (by simp)]
          . simp [hx]
        . simp
    }
    rw [card_eq_of_equiv h2, card_product, ih, pow_succ]
    rw [card_sdiff (by simpa using h1)]; simp; omega



-- Bijections between finite sets

noncomputable def FinBijOn {α : Type _} {β : Type _} (s : Finset α) (t : Finset β) [Inhabited β] :=
  {f ∈ FinOn s t | Set.BijOn f s t}

theorem card_FinBijOn {α : Type _} {β : Type _} (s : Finset α) (t : Finset β) [Inhabited β]
    (n : ℕ) (hs : #s = n) (ht : #t = n)
    : #(FinBijOn s t) = n.factorial := by
  induction' n with n ih generalizing s t
  . suffices ∃ y, FinBijOn s t = {y} from by simpa [card_eq_one]
    replace hs : s = ∅ := card_eq_zero.mp hs
    subst hs
    replace ht : t = ∅ := card_eq_zero.mp ht
    subst ht
    use λ _ ↦ default
    ext f
    suffices (∀ x, f x = default) ↔ f = λ x ↦ default from by simpa [FinBijOn, FinOn, FunOn]
    simp [funext_iff]
  . have h1 : s.Nonempty := by apply card_ne_zero.mp; omega
    let x0 : α := h1.choose
    have h2 : x0 ∈ s := h1.choose_spec
    let h3 : FinBijOn s t ≃ t.sigma λ y ↦ FinBijOn (s \ {x0}) (t \ {y})
      := {
      toFun := λ ⟨f, hf⟩ ↦ ⟨⟨f x0, λ x ↦ if x = x0 then default else f x⟩, by
        simp [FinBijOn, FinOn, FunOn] at hf
        simp [FinBijOn, FinOn, FunOn]
        split_ands
        . sorry
        . sorry
        . sorry
        . intro x hx
          simp at hx
          have c1 := hf.left.left _ hx.left
          have c2 : ¬f x = f x0 := by
            intro c2
            apply hx.right
            exact hf.right.right.left (by simpa using hx.left) h2 c2
          simp [hx, c1, c2]
        . intro x hx x' hx'
          simp at hx hx'
          have c1 := hf.right.right.left hx.left hx'.left
          simpa [hx.right, hx'.right] using c1
        . intro y hy
          simp at hy
          have hy' := hf.right.right.right hy.left
          obtain ⟨x, h1, h2⟩ := by simpa using hy'
          use x
          have h3 : x ≠ x0 := by
            intro h3
            subst h3
            apply hy.right
            simp [h2]
          split_ands
          . simpa using h1
          . intro h4
            simp at h4
            apply h3 h4
          . simp [h3, h2]⟩
      invFun := sorry
      left_inv := sorry
      right_inv := sorry
    }
    rw [card_eq_of_equiv h3]
    rw [card_sigma]
    calc
      _ = ∑ y ∈ t, n.factorial := by
        apply sum_congr rfl
        intro y hy
        exact ih (s \ {x0}) (t \ {y})
          (by rw [card_sdiff (by simpa using h2)]; simp; omega)
          (by rw [card_sdiff (by simpa using hy)]; simp; omega)
      _ = _ := by simp only [sum_const, smul_eq_mul, ht, Nat.factorial_succ]
