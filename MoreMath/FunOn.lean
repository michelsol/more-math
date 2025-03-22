import Mathlib

open Nat

namespace Finset

-- Functions from a finite set to a finite set
noncomputable def funOn {α β : Type _} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β) : Finset (α → β) :=
  let F := {f : α → β | ∀ x, if x ∈ s then f x ∈ t else f x = 0}
  let g : F ≃ (s → t) := {
      toFun := λ ⟨f, hf⟩ ⟨x, hx⟩ ↦ ⟨f x, by simpa [hx] using hf x⟩
      invFun := λ f ↦ ⟨λ x ↦ if hx : x ∈ s then (f ⟨x, hx⟩).1 else 0, by intro x; by_cases hx : x ∈ s <;> simp [hx]⟩
      left_inv := by intro ⟨f, hf⟩; ext x; specialize hf x; by_cases hx : x ∈ s <;> simp [hx] at hf ⊢; simp [hf]
      right_inv := by intro f; simp
    }
  letI := g.finite_iff.mpr inferInstance
  letI := Fintype.ofFinite F
  F.toFinset

theorem funOn_mapsTo {α β : Type _} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β)
    {f : α → β} (hf : f ∈ funOn s t) {x} (hx : x ∈ s) : f x ∈ t := by
  simp [funOn] at hf
  simpa [hx] using hf x

theorem funOn_zero_of_not_mem {α β : Type _} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β)
    {f : α → β} (hf : f ∈ funOn s t) {x} (hx : x ∉ s) : f x = 0 := by
  simp [funOn] at hf
  simpa [hx] using hf x

theorem card_funOn {α β : Type _} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β) :
    #(funOn s t) = #t ^ #s := by
  classical
  suffices ∀ n, #s = n → #(funOn s t) = #t ^ n from this #s rfl
  intro n
  induction' n with n ih generalizing s t <;> intro hs
  . replace hs : s = ∅ := by simpa using hs
    suffices ∃ f, funOn s t = {f} from by simpa [hs, card_eq_one]
    subst hs; use λ _ ↦ 0; ext f; simp [funOn, funext_iff]
  . have h0 : s.Nonempty := by apply nonempty_of_ne_empty; apply_fun (#.); dsimp; omega
    let x0 := h0.choose
    have hx0 : x0 ∈ s := h0.choose_spec
    let h1 : funOn s t ≃ (funOn (s \ {x0}) t) ×ˢ t := {
      toFun := λ ⟨f, hf⟩ ↦ ⟨⟨λ x ↦ if x = x0 then 0 else f x, f x0⟩, by
        replace hf := by simpa [funOn] using hf
        simp [funOn]
        split_ands
        . intro x
          specialize hf x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2] at hf ⊢ <;> simpa using hf
        . simpa [hx0] using hf x0⟩
      invFun := λ ⟨⟨g, y0⟩, hg⟩ =>
        ⟨λ x ↦ if x = x0 then y0 else g x, by
          obtain ⟨hg, hy0⟩ := by simpa [funOn] using hg
          simp [funOn]
          intro x
          specialize hg x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2, hx0, hy0] at hg ⊢ <;> simpa using hg⟩
      left_inv := by
        intro ⟨f, hf⟩
        ext x
        by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
        all_goals simp [hx2]
      right_inv := by
        intro ⟨⟨g, y0⟩, hg⟩
        obtain ⟨hg, hy0⟩ := by simpa [funOn] using hg
        ext x
        . specialize hg x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2] at hg ⊢ <;> simp [hg]
        . simp
    }
    rw [card_eq_of_equiv h1, card_product, ih, pow_succ]
    rw [card_sdiff (by simpa using hx0)]; simp; omega



-- Bijections between finite sets
open Classical in
noncomputable def bijOn {α β : Type _} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β) :=
  {f ∈ funOn s t | Set.BijOn f s t}

theorem card_bijOn {α β : Type _} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β)
    {n : ℕ} (hs : #s = n) (ht : #t = n) : #(bijOn s t) = n ! := by
  classical
  induction' n with n ih generalizing s t
  . suffices ∃ y, bijOn s t = {y} from by simpa [card_eq_one]
    replace hs : s = ∅ := card_eq_zero.mp hs
    subst hs
    replace ht : t = ∅ := card_eq_zero.mp ht
    subst ht
    use λ _ ↦ 0; ext f; simp [bijOn, funOn, funext_iff]
  . have hs : s.Nonempty := by apply Finset.card_ne_zero.mp; omega
    let x0 := hs.choose
    have hx0 : x0 ∈ s := hs.choose_spec
    let h : bijOn s t ≃ t.sigma λ y ↦ bijOn (s \ {x0}) (t \ {y}) := {
      toFun := λ ⟨f, hf⟩ ↦ ⟨⟨f x0, λ x ↦ if x = x0 then 0 else f x⟩, by
        obtain ⟨hf1, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp [bijOn, funOn]
        split_ands
        . simpa [hx0] using hf1 x0
        . intro x
          specialize hf1 x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2] at hf1 ⊢
          all_goals simp [hf1]
          contrapose! hx2
          exact hf2.right.left hx hx0 hx2
        . intro x hx
          obtain ⟨hx, hx2⟩ := by simpa using hx
          specialize hf1 x
          simp [hx] at hf1
          simp [hx2, hf1]
          contrapose! hx2
          exact hf2.right.left hx hx0 hx2
        . intro x hx x' hx'
          obtain ⟨hx, hx2⟩ := by simpa using hx
          obtain ⟨hx', hx2'⟩ := by simpa using hx'
          intro h
          simp [hx2, hx2'] at h
          exact hf2.right.left (by simpa using hx) (by simpa using hx') h
        . intro y hy
          obtain ⟨hy, hy2⟩ := by simpa using hy
          obtain ⟨x, hx, hx2⟩ := hf2.right.right hy
          use x
          have hxx0 : x ≠ x0 := by
            contrapose! hy2
            subst hy2
            simp [hx2]
          split_ands
          . simpa using hx
          . simp [hxx0]
          . simp [hxx0, hx2]⟩
      invFun := λ ⟨⟨y0, f⟩, hyf⟩ ↦ ⟨λ x ↦ if x = x0 then y0 else f x, by
        obtain ⟨hy0, hf⟩ := by simpa using hyf
        obtain ⟨hf, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp [bijOn, funOn]
        split_ands
        . intro x
          specialize hf x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2, hx0, hy0] at hf ⊢ <;> simp [hf]
        . intro x hx
          simp at hx
          specialize hf x
          by_cases hx2 : x = x0
          all_goals simp [hx2, hy0, hx] at hf ⊢ <;> simp [hf]
        . intro x hx x' hx' h
          simp at hx hx'
          simp at h
          have hfx := hf x
          have hfx' := hf x'
          by_cases hx2 : x = x0 <;> by_cases hx2' : x' = x0
          all_goals simp [hx, hx2, hx', hx2'] at hfx hfx' h
          . simp [hx2, hx2']
          . tauto
          . tauto
          . exact hf2.right.left (by simp [hx, hx2]) (by simp [hx', hx2']) h
        . intro y hy
          by_cases hy2 : y = y0
          . use x0
            simp [hx0, hy2]
          . obtain ⟨x, hx, hx2⟩ : ∃ x, (x ∈ s ∧ ¬x = x0) ∧ f x = y := by
              simpa using hf2.right.right (by simp [hy, hy2])
            use x
            simp [hx, hx2]⟩
      left_inv := by
        simp [Function.LeftInverse]
        intro f hf
        ext x
        by_cases hx : x = x0
        all_goals simp [hx]
      right_inv := by
        intro ⟨⟨y, f⟩, hyf⟩
        obtain ⟨hy0, hf⟩ := by simpa using hyf
        obtain ⟨hf, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp [Function.RightInverse, Function.LeftInverse]
        ext x
        specialize hf x
        by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
        all_goals simp [hx, hx2] at hf ⊢ <;> simp [hf]
    }
    rw [card_eq_of_equiv h]
    rw [card_sigma]
    calc
      _ = ∑ y ∈ t, n.factorial := by
        apply sum_congr rfl
        intro y hy
        exact ih (s \ {x0}) (t \ {y})
          (by rw [card_sdiff (by simpa using hx0)]; simp; omega)
          (by rw [card_sdiff (by simpa using hy)]; simp; omega)
      _ = _ := by simp only [sum_const, smul_eq_mul, ht, Nat.factorial_succ]

end Finset
