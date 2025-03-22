import Mathlib

open Nat Function

namespace Finset

theorem card_eq_of_bijOn [Zero α] {s : Finset α} {t : Finset β} {f : α → β} (hf : Set.BijOn f s t) :
    #s = #t := by
  apply card_eq_of_equiv
  exact {
    toFun := λ ⟨x, hx⟩ ↦ ⟨f x, by simpa using hf.left hx⟩
    invFun := λ ⟨y, hy⟩ ↦ ⟨f.invFunOn s y, invFunOn_mem (hf.right.right hy)⟩
    left_inv := by intro ⟨x, hx⟩; simpa using hf.invOn_invFunOn.left hx
    right_inv := by intro ⟨y, hy⟩; simpa using hf.invOn_invFunOn.right hy
  }

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

theorem mem_funOn_iff {α β : Type _} [DecidableEq α] [Zero β] {s : Finset α} {t : Finset β}
    (f : α → β) : f ∈ funOn s t ↔ ∀ x, if x ∈ s then f x ∈ t else f x = 0 := by
  simp [funOn]

theorem mem_funOn_iff' {α β : Type _} [DecidableEq α] [Zero β] {s : Finset α} {t : Finset β}
    (f : α → β) : f ∈ funOn s t ↔ (∀ x ∈ s, f x ∈ t) ∧ ∀ x ∉ s, f x = 0 := by
  constructor
  . intro hf
    split_ands <;> intro x hx
    all_goals
      simp only [mem_funOn_iff] at hf
      simpa [hx] using hf x
  . intro ⟨hf1, hf2⟩
    simp only [mem_funOn_iff]
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
    . simp [hf1 x hx]
    . simp [hf2 x hx]


-- Given x0 ∈ s,
-- choosing a function from s → t, is equivalent to
-- choosing a function from s \ {x0} → t, and an element of t to assign to x0
def funOn_equiv_product_sdiff {α β : Type _} [DecidableEq α] [Zero β]
    (s : Finset α) (t : Finset β) {x0 : α} (hx0 : x0 ∈ s) :
  funOn s t ≃ (funOn (s \ {x0}) t) ×ˢ t := {
      toFun := λ ⟨f, hf⟩ ↦ ⟨⟨λ x ↦ if x = x0 then 0 else f x, f x0⟩, by
        replace hf := by simpa [funOn] using hf
        simp only [mem_product, mem_funOn_iff]
        split_ands
        . intro x
          specialize hf x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2] at hf ⊢ <;> simpa using hf
        . simpa [hx0] using hf x0⟩
      invFun := λ ⟨⟨g, y0⟩, hg⟩ =>
        ⟨λ x ↦ if x = x0 then y0 else g x, by
          obtain ⟨hg, hy0⟩ := by simpa [funOn] using hg
          simp only [mem_funOn_iff]
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


-- There are #t ^ #s functions in s → t
theorem card_funOn {α β : Type _} [DecidableEq α] [Zero β] (s : Finset α) (t : Finset β) :
    #(funOn s t) = #t ^ #s := by
  suffices ∀ n, #s = n → #(funOn s t) = #t ^ n from this #s rfl
  intro n
  induction' n with n ih generalizing s t <;> intro hs
  . replace hs : s = ∅ := by simpa using hs
    suffices ∃ f, funOn s t = {f} from by simpa [hs, card_eq_one]
    subst hs; use λ _ ↦ 0; ext f; simp [funOn, funext_iff]
  . have h0 : s.Nonempty := by apply nonempty_of_ne_empty; apply_fun (#.); dsimp; omega
    let x0 := h0.choose
    have hx0 : x0 ∈ s := h0.choose_spec
    let h1 := funOn_equiv_product_sdiff s t hx0
    replace h1 := card_eq_of_equiv h1
    rw [h1, card_product, ih, pow_succ]
    rw [card_sdiff (by simpa using hx0)]; simp; omega




-- Bijections between finite sets
noncomputable def bijOn {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β] (s : Finset α) (t : Finset β) :=
  {f ∈ funOn s t | Set.BijOn f s t}

theorem mem_bijOn_iff {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β] {s : Finset α} {t : Finset β}
    (f : α → β) : f ∈ bijOn s t ↔ (f ∈ funOn s t ∧ Set.BijOn f s t) := by
  simp [bijOn]

-- Given x0 ∈ s,
-- choosing a bijection from s → t, is equivalent to
-- choosing an element y ∈ t to assign to x0, together with a bijection from s \ {x0} → t \ {f x0}
def bijOn_equiv_sigma_sdiff {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β]
    (s : Finset α) (t : Finset β) {x0 : α} (hx0 : x0 ∈ s) :
  bijOn s t ≃ t.sigma λ y ↦ bijOn (s \ {x0}) (t \ {y}) := {
      toFun := λ ⟨f, hf⟩ ↦ ⟨⟨f x0, λ x ↦ if x = x0 then 0 else f x⟩, by
        obtain ⟨hf1, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp only [mem_sigma, mem_bijOn_iff, mem_funOn_iff]
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
          . simp at hx
            simp [hx, hxx0]
          . simp [hxx0, hx2]⟩
      invFun := λ ⟨⟨y0, f⟩, hyf⟩ ↦ ⟨λ x ↦ if x = x0 then y0 else f x, by
        obtain ⟨hy0, hf⟩ := by simpa using hyf
        obtain ⟨hf, hf2⟩ := by simpa [bijOn, funOn] using hf
        simp only [mem_bijOn_iff, mem_funOn_iff]
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


-- The number of bijections between two finite sets of size n is n!.
theorem card_bijOn {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β] (s : Finset α) (t : Finset β)
    {n : ℕ} (hs : #s = n) (ht : #t = n) : #(bijOn s t) = n ! := by
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
    calc
      #(bijOn s t) = #(t.sigma λ y0 ↦ bijOn (s \ {x0}) (t \ {y0})) := by
        apply card_eq_of_equiv
        exact bijOn_equiv_sigma_sdiff s t hx0
      _ = ∑ y0 ∈ t, #(bijOn (s \ {x0}) (t \ {y0})) := by apply card_sigma
      _ = ∑ y0 ∈ t, n ! := by
        apply sum_congr rfl
        intro y0 hy0
        exact ih (s \ {x0}) (t \ {y0})
          (by rw [card_sdiff (by simpa using hx0)]; simp; omega)
          (by rw [card_sdiff (by simpa using hy0)]; simp; omega)
      _ = (n + 1) ! := by simp only [sum_const, smul_eq_mul, ht, Nat.factorial_succ]


-- Injections between finite sets
noncomputable def injOn {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β] (s : Finset α) (t : Finset β) :=
  {f ∈ funOn s t | Set.InjOn f s}

theorem mem_injOn_iff {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β] {s : Finset α} {t : Finset β}
    (f : α → β) : f ∈ injOn s t ↔ (f ∈ funOn s t ∧ Set.InjOn f s) := by
  simp [injOn]


-- Given x0 ∈ s,
-- choosing a injection from s → t, is equivalent to
-- choosing an element y ∈ t to assign to x0, together with an injection from s \ {x0} → t \ {f x0}
def injOn_equiv_sigma_sdiff {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β]
    (s : Finset α) (t : Finset β) {x0 : α} (hx0 : x0 ∈ s) :
  injOn s t ≃ t.sigma λ y ↦ injOn (s \ {x0}) (t \ {y}) := {
      toFun := λ ⟨f, hf⟩ ↦ ⟨⟨f x0, λ x ↦ if x = x0 then 0 else f x⟩, by
        obtain ⟨hf1, hf2⟩ := by simpa [injOn, funOn] using hf
        simp only [mem_sigma, mem_injOn_iff, mem_funOn_iff]
        split_ands
        . simpa [hx0] using hf1 x0
        . intro x
          specialize hf1 x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2] at hf1 ⊢
          all_goals simp [hf1]
          contrapose! hx2
          exact hf2 hx hx0 hx2
        . intro x hx x' hx'
          obtain ⟨hx, hx2⟩ := by simpa using hx
          obtain ⟨hx', hx2'⟩ := by simpa using hx'
          intro h
          simp [hx2, hx2'] at h
          exact hf2 (by simpa using hx) (by simpa using hx') h⟩
      invFun := λ ⟨⟨y0, f⟩, hyf⟩ ↦ ⟨λ x ↦ if x = x0 then y0 else f x, by
        obtain ⟨hy0, hf⟩ := by simpa using hyf
        obtain ⟨hf, hf2⟩ := by simpa [injOn, funOn] using hf
        simp only [mem_injOn_iff, mem_funOn_iff]
        split_ands
        . intro x
          specialize hf x
          by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
          all_goals simp [hx, hx2, hx0, hy0] at hf ⊢ <;> simp [hf]
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
          . exact hf2 (by simp [hx, hx2]) (by simp [hx', hx2']) h⟩
      left_inv := by
        simp [Function.LeftInverse]
        intro f hf
        ext x
        by_cases hx : x = x0
        all_goals simp [hx]
      right_inv := by
        intro ⟨⟨y, f⟩, hyf⟩
        obtain ⟨hy0, hf⟩ := by simpa using hyf
        obtain ⟨hf, hf2⟩ := by simpa [injOn, funOn] using hf
        simp [Function.RightInverse, Function.LeftInverse]
        ext x
        specialize hf x
        by_cases hx : x ∈ s <;> by_cases hx2 : x = x0
        all_goals simp [hx, hx2] at hf ⊢ <;> simp [hf]
    }


-- The number of injections from a set of size m to a set of size n is n! / (n - m)!
theorem card_injOn {α β : Type _} [DecidableEq α] [DecidableEq β] [Zero β] (s : Finset α) (t : Finset β)
    (h : #s ≤ #t) : #(injOn s t) = (#t) ! / (#t - #s) ! := by
  suffices ∀ n, ∀ m ≤ n, ∀ t : Finset β, #t = n → ∀ s : Finset α, #s = m →
      #(injOn s t) = n ! / (n - m) ! from this #t #s h t rfl s rfl
  intro n
  induction' n with n ih
  . intro m hm t htn s hsm
    replace hm : m = 0 := by omega
    subst hm
    suffices #(s.injOn t) = 1 from by simpa
    rw [card_eq_one]
    rw [card_eq_zero] at hsm
    subst hsm
    use λ _ ↦ 0; ext f; simp [injOn, funOn, funext_iff]
  . intro m hm t htn s hsm
    by_cases hm2 : m = 0
    . subst hm2
      suffices #(s.injOn t) = 1 from by
        simp only [this, tsub_zero]
        refine Eq.symm (Nat.div_self ?_)
        exact factorial_pos (n + 1)
      rw [card_eq_one]
      rw [card_eq_zero] at hsm
      subst hsm
      use λ _ ↦ 0; ext f; simp [injOn, funOn, funext_iff]
    have hs : s.Nonempty := by apply Finset.card_ne_zero.mp; omega
    let x0 := hs.choose
    have hx0 : x0 ∈ s := hs.choose_spec
    calc
      #(injOn s t) = #(t.sigma λ y0 ↦ injOn (s \ {x0}) (t \ {y0})) := by
        apply card_eq_of_equiv
        exact injOn_equiv_sigma_sdiff s t hx0
      _ = ∑ y0 ∈ t, #(injOn (s \ {x0}) (t \ {y0})) := by apply card_sigma
      _ = ∑ y0 ∈ t, n ! / (n + 1 - m) ! := by
        apply sum_congr rfl
        intro y0 hy0
        specialize ih (m - 1) (by omega)
          (t \ {y0}) (by rw [card_sdiff (by simpa using hy0)]; simp; omega)
          (s \ {x0}) (by rw [card_sdiff (by simpa using hx0)]; simp; omega)
        rw [ih]
        congr 2
        omega
      _ = (n + 1) * (n ! / (n + 1 - m) !)  := by simp [htn]
      _ = (n + 1) * n ! / (n + 1 - m) ! := by
        refine Eq.symm (Nat.mul_div_assoc (n + 1) ?_)
        refine factorial_dvd_factorial ?_
        omega
      _ = (n + 1) ! / (n + 1 - m) ! := rfl


-- WIP
-- Given a finite set t and k ≤ #t
-- choosing an injection [1,k] → t, is equivalent to
-- choosing a set s of size k in t, together with an injection [1,k] → s
def injOn_equiv_sigma_powerset_with_card {β : Type _} [DecidableEq β] [Zero β]
    (t : Finset β) (k : ℕ) (hk : k ≤ #t) :
  injOn (Icc 1 k) t ≃ { s ∈ t.powerset | #s = k }.sigma λ s ↦ injOn (Icc 1 k) s := {
    toFun := λ ⟨f, h⟩ ↦ ⟨⟨(Icc 1 k).image f, f⟩, by
      simp only [mem_sigma]
      simp only [mem_injOn_iff, mem_funOn_iff] at h ⊢
      split_ands
      . sorry
      . sorry
      . sorry
      ⟩
    invFun := λ ⟨⟨s, f⟩, h⟩ ↦ ⟨f, by
      simp [mem_injOn_iff, mem_funOn_iff] at h ⊢
      sorry⟩
    left_inv := by simp [LeftInverse]
    right_inv := by
      intro ⟨⟨s, f⟩, h1⟩
      simp [Function.RightInverse, LeftInverse, mem_injOn_iff, mem_funOn_iff] at h1 ⊢
      ext x
      sorry
  }

end Finset
