import Mathlib

open Bornology Metric ENNReal in
/-- A non empty bounded set of ℝᵈ is contained in a closed ball with miminal radius -/
theorem smallest_enclosing_ball_of_isBounded
    {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hS : IsBounded S) (hS2 : S.Nonempty) :
    ∃ (c0 r0 : _) (_ : S ⊆ closedBall c0 r0), ∀ c, ∀ r, S ⊆ closedBall c r → r0 ≤ r := by

  -- Choose an arbitrary point in S
  let s0 := hS2.choose
  have hs0 : s0 ∈ S := hS2.choose_spec

  -- Define a function  c ↦ sup {edist(s, c) | s ∈ S}
  -- possibly taking values in ℝ≥0∞ (called g) but coerced back to ℝ (called f)
  -- Calculations steps involving sup and inf will be carried out in ℝ≥0∞ to simplify logic
  let g c := sSup {edist s c | s ∈ S}
  let f c := (g c).toReal

  -- g is actually real valued, as S is bounded
  have hg1 c : g c ≠ ⊤ := by
    by_contra! h1
    rw [sSup_eq_top] at h1
    contrapose! h1
    use EMetric.diam S + edist s0 c
    use by
      apply add_lt_top.mpr
      split_ands
      · rw [lt_top_iff_ne_top, ←isBounded_iff_ediam_ne_top]
        exact hS
      · apply edist_lt_top
    intro t ⟨s, hs, hs2⟩
    subst hs2
    calc
      edist s c ≤ edist s s0 + edist s0 c := by apply edist_triangle
      _ ≤ _ := by gcongr 1; exact EMetric.edist_le_diam_of_mem hs hs0

  -- so g and f are equal up to coercion
  have hg2 c : g c = ENNReal.ofReal (f c) := by rw [ofReal_toReal]; exact hg1 c

  -- and so are their infima
  have hg3 : sInf (Set.range g) = ENNReal.ofReal (sInf (Set.range f)) := calc
    _ = ENNReal.ofReal (sInf (Set.range g)).toReal := by
      rw [ofReal_toReal]
      by_contra! h1
      rw [sInf_eq_top] at h1
      contrapose! h1
      use g s0, by simp, hg1 s0
    _ = ENNReal.ofReal (sInf (ENNReal.toReal '' Set.range g)) := by
      rw [toReal_sInf]
      intro y ⟨x, hx⟩
      subst hx
      apply hg1 x
    _ = ENNReal.ofReal (sInf (Set.range (ENNReal.toReal ∘ g))) := by rw [Set.range_comp]
    _ = _ := by congr 1

  -- Now the problem reduces to showing that f attains its minimum
  suffices sInf (Set.range f) ∈ Set.range f by
    obtain ⟨cm, h1⟩ := this
    use cm, f cm
    have h2 : S ⊆ closedBall cm (f cm) := by
      intro c hc
      rw [mem_closedBall]
      rw [←ofReal_le_iff_le_toReal (hg1 cm), ←edist_dist]
      rw [le_sSup_iff]
      intro s hs
      simp [upperBounds] at hs
      simpa using hs c hc
    use h2
    intro c r h3
    apply toReal_le_of_le_ofReal
    · calc
        _ ≤ dist s0 c := by apply dist_nonneg
        _ ≤ r := by simpa [mem_closedBall] using h3 hs0
    replace h1 : g cm = sInf (Set.range g) := by rw [hg2, h1, hg3]
    rw [h1]
    rw [sInf_le_iff]
    intro s hs
    simp [lowerBounds] at hs
    unfold g at hs
    specialize hs c
    simp [le_sSup_iff, upperBounds] at hs
    apply hs
    intro a ha
    specialize h3 ha
    rw [mem_closedBall] at h3
    rw [edist_dist]
    exact ofReal_le_ofReal h3

  -- The global minimum must be attained within a closed ball around s0
  -- as f grows when going far from s0
  let K := closedBall s0 (2 * f s0)
  suffices sInf (f '' K) ∈ f '' K by
    apply Set.mem_range_of_mem_image f K
    convert this using 1
    refine csInf_eq_csInf_of_forall_exists_le ?_ ?_
    swap
    · intro _ ⟨y, hy1, hy2⟩
      subst hy2
      use f y
      simp
    · intro _ ⟨c, hc⟩
      subst hc
      by_cases hc2 : c ∈ K
      · use f c
        split_ands
        · use c
        · simp
      · replace hc2 : dist c s0 > 2 * f s0 := by simpa [K] using hc2
        use f s0
        split_ands
        · use s0
          split_ands
          · simp [K]
            apply toReal_nonneg
          · simp
        · calc
            f c = (g c).toReal := rfl
            _ ≥ (edist s0 c - g s0).toReal := by
              gcongr 1
              · apply hg1
              change _ ≤ _
              rw [le_sSup_iff]
              intro b hb
              simp [upperBounds] at hb
              calc
                _ ≤ edist s0 c := by apply tsub_le_self
                _ ≤ b := hb s0 hs0
            _ = (edist c s0).toReal - (g s0).toReal := by
              rw [toReal_sub_of_le]
              · rw [edist_comm]
              · suffices f s0 ≤ dist s0 c by
                  rw [←toReal_le_toReal (hg1 s0) (by apply edist_ne_top)]
                  rw [edist_dist, toReal_ofReal (by apply dist_nonneg)]
                  simpa using this
                rw [dist_comm]
                have : f s0 ≥ 0 := by simp [f]
                linarith
              · apply edist_ne_top
            _ = dist c s0 - f s0 := by
              congr 1
              simp [edist_dist]
            _ ≥ _ := by linarith

  -- We now use Weierstrass' theorem to show that f attains its global minimum on the compact set K
  apply IsCompact.sInf_mem
  · apply IsCompact.image_of_continuousOn
    · apply isCompact_closedBall
    · apply Continuous.continuousOn
      apply UniformContinuous.continuous
      apply LipschitzWith.uniformContinuous (K := (1 : ℝ).toNNReal)
      apply LipschitzWith.of_dist_le'
      intro x y
      calc
        |f x - f y| ≤ dist x y := by
          revert x y
          suffices ∀ x y, f x - f y ≤ dist x y by
            intro x y
            rw [abs_le]
            split_ands
            · specialize this y x
              rw [dist_comm]
              linarith
            · exact this x y
          intro x y
          suffices f x ≤ f y + dist x y by linarith
          calc
            f x = (g x).toReal := rfl
            _ ≤ (g y + edist x y).toReal := by
              gcongr 1
              · exact add_ne_top.mpr ⟨by apply hg1, by apply edist_ne_top⟩
              calc
                g x = sSup {edist s x | s ∈ S} := by rfl
                _ ≤ sSup {edist s y | s ∈ S} + edist x y := by
                  rw [sSup_le_iff]
                  intro _ ⟨s, hs, hs2⟩; subst hs2
                  calc
                    edist s x ≤ edist s y + edist y x := by apply edist_triangle
                    _ = edist s y + edist x y := by congr 1; rw [edist_comm]
                    _ ≤ _ := by
                      gcongr 1
                      rw [le_sSup_iff]
                      intro t ht
                      simp [upperBounds] at ht
                      exact ht s hs
                _ = g y + edist x y := rfl
            _ = (g y).toReal + (edist x y).toReal := toReal_add (hg1 y) (by apply edist_ne_top)
            _ = _ := by congr 1; simp [edist_dist]
        _ = _ := by simp
  · use f s0, s0, by simp [K, f]


open Bornology Metric ENNReal in
/-- The minimal enclosing ball of a non empty set of ℝᵈ is unique -/
theorem unique_smallest_enclosing_ball_of_isBounded
    {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hS2 : S.Nonempty)
    {x r1 y r2}
    (h1 : S ⊆ closedBall x r1)
    (h2 : ∀ c r, S ⊆ closedBall c r → r1 ≤ r)
    (h3 : S ⊆ closedBall y r2)
    (h4 : ∀ c r, S ⊆ closedBall c r → r2 ≤ r) :
    r1 = r2 ∧ x = y := by
  have h : r1 = r2 := by
    specialize h2 y r2 h3
    specialize h4 x r1 h1
    exact le_antisymm h2 h4
  use h
  subst h

  -- Choose an arbitrary point in S
  let s0 := hS2.choose
  have hs0 : s0 ∈ S := hS2.choose_spec
  have hr1 : r1 ≥ 0 := calc
      0 ≤ dist s0 y := by apply dist_nonneg
      _ ≤ r1 := by simpa [mem_closedBall] using h3 hs0

  let α := dist x y / 2
  let c := (1 / 2 : ℝ) • (x + y)
  set B1 := closedBall x r1
  set B2 := closedBall y r1

  have h5 z (hz1 : z ∈ B1) (hz2 : z ∈ B2) : dist z c ^ 2 ≤ r1 ^ 2 - α ^ 2 := calc
    ‖z - c‖ ^ 2 = ‖(1 / 2 : ℝ) • (z - x + (z - y))‖ ^ 2 := by congr 2; module
    _ = ‖(1 / 2 : ℝ)‖ ^ 2 * ‖(z - x + (z - y))‖ ^ 2 := by rw [norm_smul]; ring
    _ = (1 / 4 : ℝ) * ‖(z - x + (z - y))‖ ^ 2 := by congr 1; norm_num
    _ = (1 / 4 : ℝ) * (2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 - ‖x - y‖ ^ 2) := by
      congr 1
      set a := z - x
      set b := z - y
      convert_to ‖a + b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 - ‖a - b‖ ^ 2 using 3
      · rw [norm_sub_rev]
        congr 1
        module
      generalize a = a, b = b
      rw [norm_add_sq_real, norm_sub_sq_real]
      ring
    _ = (1 / 2 : ℝ) * ‖z - x‖ ^ 2 + (1 / 2 : ℝ) * ‖z - y‖ ^ 2 - (1 / 4 : ℝ) * ‖x - y‖ ^ 2 := by ring
    _ ≤ (1 / 2 : ℝ) * r1 ^ 2 + (1 / 2 : ℝ) * r1 ^ 2 - (1 / 4 : ℝ) * (2 * α) ^ 2 := by
      gcongr 4
      · simpa [mem_closedBall] using hz1
      · simpa [mem_closedBall] using hz2
      · apply le_of_eq
        calc
          _ = dist x y := by ring
          _ = ‖x - y‖ := rfl
    _ = r1 ^ 2 - α ^ 2 := by ring

  have h6 : S ⊆ closedBall c √(r1 ^ 2 - α ^ 2) := by
    intro s hs
    rw [mem_closedBall]
    calc
      _ = √(dist s c ^ 2) := by
        symm
        apply Real.sqrt_sq
        apply dist_nonneg
      _ ≤ √(r1 ^ 2 - α ^ 2) := Real.sqrt_le_sqrt (h5 s (h1 hs) (h3 hs))

  specialize h2 c (√(r1 ^ 2 - α ^ 2)) h6
  replace h2 := calc
    r1 ^ 2 ≤ √(r1 ^ 2 - α ^ 2) ^ 2 := by gcongr 1
    _ = r1 ^ 2 - α ^ 2 := by
      apply Real.sq_sqrt
      calc
        0 ≤ dist s0 c ^ 2 := by apply sq_nonneg
        _ ≤ _ := h5 s0 (h1 hs0) (h3 hs0)
  replace h2 : α = 0 := by nlinarith
  unfold α at h2
  replace h2 : dist x y = 0 := by linarith
  simpa [dist_eq_zero] using h2


open Bornology Metric ENNReal Finset InnerProductSpace in
/-- (Jung’s theorem) Suppose $$S\subset\mathbb{R}^{d}$$ is bounded with diameter $$\text{diam}(S)$$.
Then $S$ is contained in a closed ball of radius $$(\frac{d}{2d+2})^{\frac{1}{2}}\text{diam}(S)$$
-/
theorem jung_theorem
    {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hS : IsBounded S) (hS2 : S.Nonempty) :
    ∃ c, S ⊆ closedBall c ((d / (2 * d + 2) : ℝ) ^ (1 / 2) * diam S) := by

  -- need to handle separately the trivial case  $$|S| = 1$$ .
  -- We first prove Jung’s theorem in the case $$S$$ is finite and $$\left|S\right|\leq d+1$$.
  by_cases h1 : S.Finite ∧ Nat.card S ≤ d + 1
  · obtain ⟨h1, h2⟩ := h1
    have h1' := h1.fintype
    replace h2 : S.toFinset.card ≤ d + 1 := by
      convert h2 using 1; symm; apply Nat.card_eq_card_toFinset

    -- Let $$c$$ denote the center of the ball containing $$S$$ of minimum radius $$r$$.
    obtain ⟨c, r, h3, h4⟩ := smallest_enclosing_ball_of_isBounded S hS hS2

    -- Translating $$S$$, we may assume without loss of generality that $$c=0$$.
    wlog hc : c = 0
    · sorry

    -- Enumerate the elements of $$\left\{x\in S: \left\|x\right\|=r\right\}$$ by
    -- $$x_{1},\cdots,x_{n}$$ (and note that $$n\geq 2$$, as shown by the lemma).
    let S' := {x ∈ S.toFinset | ‖x‖ = r}
    let n := S'.card
    have hn : n ≥ 2 := by -- here we need the fact that $$|S|\geq 2$$
      sorry
    let x' : Icc 1 n ≃ S' := ((Icc 1 n).equivFinOfCardEq (by simp [n])).trans S'.equivFin.symm
    let y k : Icc 1 n := if hk : k ∈ Icc 1 n then ⟨k, hk⟩ else ⟨1, by simp; omega⟩
    -- writing the enumaration as a composition of elementary functions
    -- so as to simplify the proofs of range / injectivity properties later on
    let x := Subtype.val ∘ x' ∘ y

    -- $$c$$ lies in the convex hull of $$x_{1},\cdots,x_{n}$$
    have h5 : c ∈ convexHull ℝ (Set.range x) := by
      sorry -- seems visually intuitive but I don't yet know how to prove it

    -- and therefore we can write
    -- $$\displaystyle c=\sum_{k=1}^{n}\lambda_{k}x_{k}$$, with $$\lambda_{k}\geq0$$,
    -- and $$ \sum_{k=1}^{n}\lambda_{k}=1$$

    obtain ⟨l, h6, h7, h8⟩ : ∃ (l : ℕ → ℝ),
        (∀ k ∈ Icc 1 n, l k ≥ 0) ∧ ∑ k ∈ Icc 1 n, l k = 1 ∧ c = ∑ k ∈ Icc 1 n, l k • x k := by
      sorry

    have h9 (i : ℕ) (hi : i ∈ Icc 1 n) := by
      simp at hi
      exact calc
      1 - l i = ∑ k ∈ Icc 1 n, l k - l i := by rw [h7]
      _ = ∑ k ∈ Icc 1 n \ {i}, l k + l i - l i := by
        have h : {i} ⊆ Icc 1 n := by intro _; simp; omega
        simp [←sum_sdiff h]
      _ = ∑ k ∈ Icc 1 n \ {i}, l k * 1 := by ring_nf
      _ ≥ ∑ k ∈ Icc 1 n \ {i}, l k * (‖x k - x i‖ ^ 2 / diam S ^ 2) := by
        gcongr 2 with k hk
        · exact h6 k (by simp at hk ⊢; omega)
        · have : diam S > 0 := sorry -- because $$|S|\geq 2$$
          suffices dist (x k) (x i) ^ 2 ≤ diam S ^ 2 by field_simp; simpa using this
          gcongr 1
          apply dist_le_diam_of_mem hS
          · sorry
          · sorry
      _ = (1 / diam S ^ 2) * ∑ k ∈ Icc 1 n \ {i}, l k * ‖x k - x i‖ ^ 2 := by
        rw [mul_sum]
        congr! 1 with k hk
        field_simp
      _ = (1 / diam S ^ 2) * ∑ k ∈ Icc 1 n, l k * ‖x k - x i‖ ^ 2 := by
        congr 1
        have h : {i} ⊆ Icc 1 n := by intro _; simp; omega
        simp [←sum_sdiff h]
      _ = (1 / diam S ^ 2) * ∑ k ∈ Icc 1 n,
            (l k * ‖x k‖ ^ 2 + l k * ‖x i‖ ^ 2 - 2 * (l k * ⟪x k, x i⟫_ℝ)) := by
        congr! 2 with k hk
        rw [norm_sub_sq_real]
        ring
      _ = (1 / diam S ^ 2) * (
            ∑ k ∈ Icc 1 n, l k * ‖x k‖ ^ 2 + ∑ k ∈ Icc 1 n, l k * ‖x i‖ ^ 2 -
            2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
        congr 1
        conv_lhs => rw [sum_sub_distrib, sum_add_distrib]
        congr 2
        rw [mul_sum]
      _ = (1 / diam S ^ 2) * (
            ∑ k ∈ Icc 1 n, l k * r ^ 2 + ∑ k ∈ Icc 1 n, l k * r ^ 2 -
            2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
        congr! 6 with k hk
        · sorry
        · sorry
      _ = (1 / diam S ^ 2) * (
            r ^ 2 * ∑ k ∈ Icc 1 n, l k + r ^ 2 * ∑ k ∈ Icc 1 n, l k -
            2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
        congr 3
        all_goals
        · rw [mul_sum]
          congr! 1 with k hk
          ring
      _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * ∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ) := by
        congr 2
        rw [h7]
        ring
      _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * (∑ k ∈ Icc 1 n, l k * ⟪x k, x i⟫_ℝ)) := by
        ring
      _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * (∑ k ∈ Icc 1 n, ⟪l k • x k, x i⟫_ℝ)) := by
        congr! 4 with k hk
        rw [real_inner_smul_left]
      _ = (1 / diam S ^ 2) * (2 * r ^ 2 - 2 * (⟪∑ k ∈ Icc 1 n, l k • x k, x i⟫_ℝ)) := by
        congr! 4 with k hk
        rw [sum_inner]
      _ = (1 / diam S ^ 2) * (2 * r ^ 2) := by simp [←h8, hc]
      _ = 2 * r ^ 2 / diam S ^ 2 := by field_simp

    sorry
  · sorry
