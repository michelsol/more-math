import MoreMath.FinsetCombinatorics

open Nat
open Finset



/-
How many permutations are there of the word "TOWN" ?
-/
example :
    let T := 0
    let O := 1
    let W := 2
    let N := 3
    let w : Fin 4 → ℕ := ![T, O, W, N]
    let X := Finset.univ.image (λ f : Equiv.Perm (Fin 4) ↦ w ∘ f)
    (#X) = 4 ! := by
  intro T O W N
  intro w X
  calc
    _ = Fintype.card {v // v ∈ X} := by symm; apply Fintype.card_coe
    _ = Fintype.card (Equiv.Perm (Fin 4)) := by
      apply Fintype.card_congr
      exact ⟨
        λ ⟨v, hv⟩ ↦
          have hv : ∃ f : Equiv.Perm (Fin 4), w ∘ f = v := by simpa [X] using hv
          hv.choose,
        λ f ↦ ⟨w ∘ f, by simp [X]⟩,
        by
          intro ⟨v, hv⟩
          have hv : ∃ f : Equiv.Perm (Fin 4), w ∘ f = v := by simpa [X] using hv
          simp [hv.choose_spec],
        by
          intro f
          have hf : ∃ g : Equiv.Perm (Fin 4), w ∘ g = w ∘ f := by use f
          have hg := hf.choose_spec
          set g := hf.choose
          show g = f
          have hw : w.Injective := by decide
          symm
          simpa using calc
            f = id ∘ f := by simp
            _ = (w.invFun ∘ w) ∘ f := by simp [Function.invFun_comp, hw]
            _ = w.invFun ∘ w ∘ f := by tauto
            _ = w.invFun ∘ w ∘ g := by rw [hg]
            _ = (w.invFun ∘ w) ∘ g := by tauto
            _ = id ∘ g := by simp [Function.invFun_comp, hw]
            _ = g := by simp
          ⟩
    _ = _ := by simp [Fintype.card_perm]




/-
How many permutations are there of the word "BAOBAB" ?
-/
example :
    let A := 0
    let B := 1
    let O := 2
    let w : Fin 6 → ℕ := ![B, A, O, B, A, B]
    let X := Finset.univ.image (λ f : Equiv.Perm (Fin 6) ↦ w ∘ f)
    (#X) = 6 ! / (3 ! * 2 !) := by
  intro A B O
  intro w X
  suffices #X * 3 ! * 2 ! = 6 ! from by
    have h1 : (3 ! * 2 ! : ℤ) ∣ 6 ! := by decide
    qify [h1] at this ⊢
    field_simp
    convert this using 1
    ring_nf
    rfl
  calc
    _ = Fintype.card {v // v ∈ X} *
        Fintype.card (Equiv.Perm (Fin 3)) * Fintype.card (Equiv.Perm (Fin 2)) := by
      generalize hX : X = X
      generalize ha : #X = a
      generalize hb : 3 ! = b
      generalize hc : 2 ! = c
      generalize ha' : Fintype.card {v // v ∈ X} = a'
      generalize hb' : Fintype.card (Equiv.Perm (Fin 3)) = b'
      generalize hc' : Fintype.card (Equiv.Perm (Fin 2)) = c'
      congr 2
      all_goals subst ha ha' hb hb' hc hc' hX
      . symm; apply Fintype.card_coe
      . simp [Fintype.card_perm]
      . simp [Fintype.card_perm]
    _ = Fintype.card ({v // v ∈ X} × (Equiv.Perm (Fin 3)) × (Equiv.Perm (Fin 2))) := by
      iterate 2 rw [Fintype.card_prod]
      ring
    _ = Fintype.card (Equiv.Perm (Fin 6)) := by
      apply Fintype.card_congr
      sorry
    _ = _ := by simp [Fintype.card_perm]
