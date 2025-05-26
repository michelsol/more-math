import Mathlib

open Filter Topology Finset

section technical_lemmas

/-- A complex or real function which is the sum of a power series `∑ aₙ xⁿ` of non zero radius,
has a taylor expansion at any order with coefficients `aₙ`. -/
theorem taylor_bigO_of_series_at_zero
    {𝕜 : Type u} [RCLike 𝕜]
    (f : 𝕜 → 𝕜) (a : ℕ → 𝕜)
    (r : ℝ) (hr : r > 0)
    (hfa : ∀ x : 𝕜, ‖x‖ < r → HasSum (λ n ↦ a n * x ^ n) (f x))
    (n : ℕ) :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, f x = ∑ k ∈ range (n + 1), a k * x ^ k + E x * x ^ (n + 1) := by

  let p := FormalMultilinearSeries.ofScalars 𝕜 a

  have hpa (k : ℕ) : p.coeff k = a k := by
    simp [p, FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

  have hpr : p.radius ≥ ENNReal.ofReal r := by
    by_cases radius_top : p.radius = ⊤
    . simp [radius_top]
    suffices p.radius.toReal ≥ r from ENNReal.ofReal_le_of_le_toReal this
    suffices ∀ r' > 0, r' < r → p.radius.toReal ≥ r' by
      contrapose! this
      use (p.radius.toReal + r) / 2
      split_ands
      . positivity
      . linarith
      . linarith
    intro r' hr' hr'2
    suffices p.radius ≥ ENNReal.ofReal r' from (ENNReal.ofReal_le_iff_le_toReal radius_top).mp this
    apply FormalMultilinearSeries.le_radius_of_summable
    suffices Summable λ n ↦ ‖a n * r' ^ n‖ from by
      simp [hr', abs_of_pos] at this
      simpa [hpa, hr'.le] using this
    rw [summable_norm_iff]
    use f r'
    apply hfa
    simp [hr', abs_of_pos, hr'2]

  have h1 : HasFPowerSeriesWithinAt f p .univ 0 := by
    use ENNReal.ofReal r
    constructor
    . simp [hpr]
    . simp [hr]
    . intro x hx hx2
      suffices HasSum (fun n => a n * x ^ n) (f x) from by
        convert this using 1
        . ext n
          simp [hpa]
          ring
        . simp
      exact hfa x (by simpa using hx2)

  have h2 : (λ y ↦ f y - p.partialSum (n + 1) y) =O[𝓝 0] λ y ↦ ‖y‖ ^ (n + 1) := by
    simpa using h1.isBigO_sub_partialSum_pow (n + 1)
  rw [Asymptotics.isBigO_iff'] at h2
  obtain ⟨c, hc, h2⟩ := h2
  use λ x ↦ (f x - p.partialSum (n + 1) x) / x ^ (n + 1)
  use c
  use by
    rw [Metric.eventually_nhds_iff] at h2 ⊢
    obtain ⟨ε, hε, h2⟩ := h2
    use ε ⊓ 1, by simp [hε]
    intro x hx
    obtain ⟨hx1, hx2⟩ : ‖x‖ < ε ∧ ‖x‖ < 1 := by simpa using hx
    specialize h2 (by simpa using hx1)
    by_cases hx3 : x = 0
    . suffices c ≥ 0 from by simpa [hx3] using this
      exact hc.le
    . apply_fun (fun y ↦ y / ‖x‖ ^ (n + 1)) at h2
      swap
      . apply monotone_div_right_of_nonneg
        positivity
      replace h2 : ‖f x - p.partialSum (n + 1) x‖ / ‖x‖ ^ (n + 1)
        ≤ c * ‖x‖ ^ (n + 1) / ‖x‖ ^ (n + 1) := by simpa using h2
      suffices ‖f x - p.partialSum (n + 1) x‖ / ‖x‖ ^ (n + 1) ≤ c from by simpa using this
      calc
        _ ≤ _ := h2
        _ = c * (‖x‖ ^ (n + 1) / ‖x‖ ^ (n + 1)) := by ring
        _ ≤ c * 1 := by
          gcongr
          calc
            _ = (1 : ℝ) := by
              apply (div_eq_one_iff_eq ?_).mpr rfl
              apply pow_ne_zero (n + 1)
              exact norm_ne_zero_iff.mpr hx3
            _ ≤ _ := by norm_num
        _ = _ := by ring

  rw [Metric.eventually_nhds_iff]
  use 1, by norm_num
  intro x hx
  replace hx : ‖x‖ < 1 := by simpa using hx
  by_cases hx2 : x = 0
  . suffices f 0 = a 0 from by simpa [hx2, zero_pow_eq] using this
    specialize hfa 0 (by simpa using hr)
    convert hfa.tsum_eq.symm using 1
    calc
      a 0 = ∑ n ∈ {0}, if n = 0 then a 0 else 0 := by simp
      _ = ∑' n : ℕ, if n = 0 then a 0 else 0 := by
        rw [tsum_eq_sum]
        intro k hk
        simp at hk
        simp [hk]
      _ = _ := by
        apply tsum_congr
        intro k
        by_cases hk : k = 0 <;> simp [hk]
  . suffices p.partialSum (n + 1) x = ∑ k ∈ range (n + 1), a k * x ^ k from by field_simp [this]
    suffices ∑ k ∈ range (n + 1), x ^ k * a k = ∑ k ∈ range (n + 1), a k * x ^ k from by
      simpa [FormalMultilinearSeries.partialSum, hpa] using this
    congr 1
    ext k
    ring

open Nat in
/-- A complex function which is holomorphic on an open ball centered at 0, has a taylor expansion
at any order with coefficients `aₖ = f'ᵏ(0) / k!`-/
theorem taylor_bigO_of_series_at_zero_of_differentiableOn_ℂ
    (f : ℂ → ℂ)
    (r : ℝ) (hr : r > 0)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, f x = ∑ k ∈ range (n + 1),
      iteratedDeriv k f 0 / k ! * x ^ k + E x * x ^ (n + 1) := by
  apply taylor_bigO_of_series_at_zero f (λ k ↦ iteratedDeriv k f 0 / k !) r hr
  intro x hx
  convert Complex.hasSum_taylorSeries_on_ball hf (by simpa using hx) using 1
  ext k
  simp
  ring

/-- Derive the little O expansion of a Taylor series from the big O expansion using `O(xⁿ⁺¹) = o(xⁿ)`-/
theorem taylor_littleO_of_bigO_at_zero {𝕜 : Type u} [RCLike 𝕜] {f r : 𝕜 → 𝕜} {n : ℕ}
    (h1 : ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
      ∀ᶠ x in 𝓝 0, f x = r x + E x * x ^ (n + 1)) :
    ∃ (o : 𝕜 → 𝕜) (_ : Tendsto o (𝓝 0) (𝓝 0)), ∀ᶠ x in 𝓝 0, f x = r x + o x * x ^ n := by
  have ⟨E, C, hE, h1⟩ := h1
  use λ x ↦ E x * x
  use by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : ∀ᶠ x in 𝓝 0, 0 ≤ ‖E x * x‖ := by
      rw [Metric.eventually_nhds_iff]
      use 1, by norm_num
      intro x hx
      apply norm_nonneg
    have h3 : ∀ᶠ x in 𝓝 0, ‖E x * x‖ ≤ C * ‖x‖ := by
      rw [Metric.eventually_nhds_iff] at hE ⊢
      obtain ⟨ε, hε, hE⟩ := hE
      use ε, hε
      intro x hx
      specialize hE hx
      calc
        _ = ‖E x‖ * ‖x‖ := by apply norm_mul
        _ ≤ C * ‖x‖ := by gcongr
    apply squeeze_zero' h2 h3
    suffices Tendsto (λ t : 𝕜 ↦ C * ‖t‖) (𝓝 0) (𝓝 (C * 0)) from by simpa using this
    apply Tendsto.const_mul
    exact tendsto_norm_zero
  convert h1 using 4 with x
  ring

/-- Derive a Taylor expansion on ℝ from a Taylor expansion on ℂ -/
theorem taylor_bigO_at_zero_ℝ_of_ℂ (f r : ℝ → ℝ) (n : ℕ)
    (h1 : ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
      ∀ᶠ x in 𝓝 0, f x = r x + E x * x ^ (n + 1)) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C), ∀ᶠ x in 𝓝 0, f x = r x + E x * x ^ (n + 1) := by
  obtain ⟨E, C, hE, h1⟩ := h1
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨ε1, hε1, h1⟩ := h1
  use λ x ↦ (f x - r x) / x ^ (n + 1)
  use C
  use by
    rw [Metric.eventually_nhds_iff] at hE ⊢
    obtain ⟨ε2, hε2, hE⟩ := hE
    use ε1 ⊓ ε2 ⊓ 1, by simp [hε1, hε2]
    intro x hx
    simp at hx
    specialize hE (y := x) (by simpa using hx.left.right)
    by_cases hx2 : x = 0
    . subst hx2
      suffices 0 ≤ C from by simpa using this
      calc
        _ ≤ _ := by simp
        _ ≤ _ := hE
    specialize h1 (y := x) (by simpa using hx.left.left)
    replace h1 : E x * x ^ (n + 1) = f x - r x := by
      linear_combination -h1
    replace h1 : E x = (f x - r x) / x ^ (n + 1) := by
      refine eq_div_of_mul_eq ?_ h1
      simp [hx2]
    rw [h1] at hE
    convert hE using 1
    norm_cast
  rw [Metric.eventually_nhds_iff]
  use ε1, hε1
  intro x hx
  specialize h1 (y := x) (by simpa using hx)
  replace h1 : E x * x ^ (n + 1) = f x - r x := by linear_combination -h1
  by_cases hx2 : x = 0
  . simp [hx2] at h1 ⊢
    norm_cast at h1
    linarith
  . field_simp

end technical_lemmas




section taylor_one_div_one_sub

/-- `1 / (1 - x) = 1 + x + x² + ... + xⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_bigO (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = ∑ k ∈ range (n + 1), x ^ k + E x * x ^ (n + 1) := by
  have h1 := taylor_bigO_of_series_at_zero (λ x : 𝕜 ↦ 1 / (1 - x)) (λ n : ℕ ↦ (1 : 𝕜)) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (λ n ↦ x ^ n) (1 - x)⁻¹ from by simpa using this
    exact hasSum_geometric_of_norm_lt_one hx
    ) n
  convert h1 using 11
  ring

/-- `1 / (1 - x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_bigO_order0 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + E x * x := by
  convert taylor_one_div_one_sub_bigO 𝕜 0 using 9 with O C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `1 / (1 - x) = 1 + x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_bigO_order1 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + x + E x * x ^ 2 := by
  convert taylor_one_div_one_sub_bigO 𝕜 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `1 / (1 - x) = 1 + x + x² + ... + xⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_littleO (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ∃ (e : 𝕜 → 𝕜) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = ∑ k ∈ range (n + 1), x ^ k + e x * x ^ n := by
    exact taylor_littleO_of_bigO_at_zero (taylor_one_div_one_sub_bigO 𝕜 n)

/-- `1 / (1 - x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_littleO_order0 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (e : 𝕜 → 𝕜) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + e x := by
  convert taylor_one_div_one_sub_littleO 𝕜 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `1 / (1 - x) = 1 + x + o(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_sub_littleO_order1 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (e : 𝕜 → 𝕜) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 - x) = 1 + x + e x * x := by
  convert taylor_one_div_one_sub_littleO 𝕜 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

end taylor_one_div_one_sub

section taylor_one_div_one_add

/-- `1 / (1 + x) = 1 - x + x² ... + (-1)ⁿxⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_bigO (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ k * x ^ k + E x * x ^ (n + 1) := by
  obtain ⟨E, C, hE, h1⟩ := taylor_one_div_one_sub_bigO 𝕜 n
  use λ x ↦ E (-x) * (-1) ^ (n + 1), C, by
    rw [Metric.eventually_nhds_iff] at hE ⊢
    obtain ⟨ε, hε, hE⟩ := hE
    use ε, hε
    intro x hx
    simpa using hE (by simpa using hx)
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  specialize h1 (y := -x) (by simpa using hx)
  convert h1 using 2
  . simp
  . apply sum_congr rfl
    intro k hk
    ring
  . ring

/-- `1 / (1 + x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_bigO_order0 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 + E x * x := by
  convert taylor_one_div_one_add_bigO 𝕜 0 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `1 / (1 + x) = 1 - x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_bigO_order1 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (E : 𝕜 → 𝕜), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 - x + E x * x ^ 2 := by
  convert taylor_one_div_one_add_bigO 𝕜 1 using 10 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]
  ring

/-- `1 / (1 + x) = 1 - x + x² ... + (-1)ⁿxⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_littleO (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    ∃ (e : 𝕜 → 𝕜) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ k * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_one_div_one_add_bigO 𝕜 n)

/-- `1 / (1 + x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_littleO_order0 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (e : 𝕜 → 𝕜) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 + e x := by
  convert taylor_one_div_one_add_littleO 𝕜 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `1 / (1 + x) = 1 - x + o(x)` as `x ⟶ 0`. -/
theorem taylor_one_div_one_add_littleO_order1 (𝕜 : Type u) [RCLike 𝕜] :
    ∃ (e : 𝕜 → 𝕜) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, 1 / (1 + x) = 1 - x + e x * x := by
  convert taylor_one_div_one_add_littleO 𝕜 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]
  ring

end taylor_one_div_one_add

section taylor_clog_one_sub
open Complex

/-- `log (1 - z) = -z - z²/2 - ... - zⁿ/n + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_clog_one_sub_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, log (1 - z) = ∑ k ∈ range (n + 1), -1 / k * z ^ k + E z * z ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℂ ↦ log (1 - x)) (λ n : ℕ ↦ -1 / n) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (λ n : ℕ ↦ x ^ n / n) (-log (1 - x)) from by
      convert this.neg using 1
      . field_simp
      . simp
    exact hasSum_taylorSeries_neg_log hx
    ) n

/-- `log (1 - z) = -z - z²/2 - ... - zⁿ/n + o(zⁿ)` as `z ⟶ 0`. -/
theorem taylor_clog_one_sub_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, log (1 - z) = ∑ k ∈ range (n + 1), -1 / k * z ^ k + e z * z ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_clog_one_sub_bigO n)

end taylor_clog_one_sub

section taylor_rlog_one_sub
open Real

/-- `log (1 - x) = -x - x²/2 - ... - xⁿ/n + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_sub_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 - x) = ∑ k ∈ range (n + 1), -1 / k * x ^ k + E x * x ^ (n + 1) := by
  have ⟨E, C, hE, h1⟩ := taylor_clog_one_sub_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ log (1 - x)) (λ x ↦ ∑ k ∈ range (n + 1), -1 / k * x ^ k) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε ⊓ 1, by simp [hε]
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx.left)
  convert h1 using 1
  . rw [Complex.ofReal_log]
    . simp
    . have hx2 := hx.right
      rw [abs_lt] at hx2
      linarith
  . norm_cast

/-- `log (1 - x) = O(x)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_sub_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 - x) = E x * x := by
  convert taylor_rlog_one_sub_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 - x) = -x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_sub_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 - x) = -x + E x * x ^ 2 := by
  convert taylor_rlog_one_sub_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `log (1 - x) = -x - x²/2 - ... - xⁿ/n + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_sub_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 - x) = ∑ k ∈ range (n + 1), -1 / k * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_rlog_one_sub_bigO n)

/-- `log (1 - x) = o(1)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_sub_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 - x) = e x := by
  convert taylor_rlog_one_sub_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 - x) = -x + o(x)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_sub_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 - x) = -x + e x * x := by
  convert taylor_rlog_one_sub_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

end taylor_rlog_one_sub

section taylor_clog_one_add
open Complex
/-- `log (1 + z) = z - z²/2 + ... + (-1)ⁿ⁺¹ zⁿ/n + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_clog_one_add_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, log (1 + z) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * z ^ k + E z * z ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℂ ↦ log (1 + x)) (λ n : ℕ ↦ (-1) ^ (n + 1) / n) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (λ n : ℕ ↦ (-1) ^ (n + 1) * x ^ n / n) (log (1 + x)) from by
      convert this using 1
      field_simp
    exact hasSum_taylorSeries_log hx
    ) n

/-- `log (1 + z) = z - z²/2 + ... + (-1)ⁿ⁺¹ zⁿ/n + o(zⁿ)` as `z ⟶ 0`. -/
theorem taylor_clog_one_add_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, log (1 + z) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * z ^ k + e z * z ^ n := by
    exact taylor_littleO_of_bigO_at_zero (taylor_clog_one_add_bigO n)

end taylor_clog_one_add

section taylor_rlog_one_add
open Real

/-- `log (1 + x) = x - x²/2 + ... + (-1)ⁿ⁺¹ xⁿ/n + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_add_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * x ^ k + E x * x ^ (n + 1) := by
  have ⟨E, C, hE, h1⟩ := taylor_clog_one_add_bigO n
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ log (1 + x)) (λ x ↦ ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * x ^ k) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε ⊓ 1, by simp [hε]
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx.left)
  convert h1 using 1
  . rw [Complex.ofReal_log]
    . simp
    . have hx2 := hx.right
      rw [abs_lt] at hx2
      linarith
  . norm_cast

/-- `log (1 + x) = O(x)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_add_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 + x) = E x * x := by
  convert taylor_rlog_one_add_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 + x) = x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_add_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, log (1 + x) = x + E x * x ^ 2 := by
  convert taylor_rlog_one_add_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `log (1 + x) = x - x²/2 + ... + (-1)ⁿ⁺¹ xⁿ/n + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_add_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 + x) = ∑ k ∈ range (n + 1), (-1) ^ (k + 1) / k * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_rlog_one_add_bigO n)

/-- `log (1 + x) = o(1)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_add_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 + x) = e x := by
  convert taylor_rlog_one_add_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `log (1 + x) = x + o(x)` as `x ⟶ 0`. -/
theorem taylor_rlog_one_add_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, log (1 + x) = x + e x * x := by
  convert taylor_rlog_one_add_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

end taylor_rlog_one_add


section taylor_cexp
open Complex Nat

/-- `exp(z) = 1 + z + z²/2 + z³/6 + ... + zⁿ/n! + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_cexp_bigO (n : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, exp z = ∑ k ∈ range (n + 1), 1 / k ! * z ^ k + E z * z ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℂ ↦ exp x) (λ n : ℕ ↦ 1 / n !) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (fun n => (n !⁻¹ : ℂ) • x ^ n) (NormedSpace.exp ℂ x) from by
      convert this using 1
      . field_simp
      . rw [exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' x
    ) n

/-- `exp(z) = 1 + z + z²/2 + z³/6 + ... + zⁿ/n! + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_cexp_littleO (n : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, exp z = ∑ k ∈ range (n + 1), 1 / k ! * z ^ k + e z * z ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_cexp_bigO n)

end taylor_cexp

section taylor_rexp
open Real Nat

/-- `exp(x) = 1 + x + x²/2 + x³/6 + ... + xⁿ/n! + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_rexp_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, exp x = ∑ k ∈ range (n + 1), 1 / k ! * x ^ k + E x * x ^ (n + 1) := by
  exact taylor_bigO_of_series_at_zero (λ x : ℝ ↦ exp x) (λ n : ℕ ↦ 1 / n !) 1 (by norm_num) (by
    intro x hx
    suffices HasSum (fun n => (n !⁻¹ : ℝ) • x ^ n) (NormedSpace.exp ℝ x) from by
      convert this using 1
      . field_simp
      . rw [exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' x
    ) n

/-- `exp(x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_rexp_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, exp x = 1 + E x * x := by
  convert taylor_rexp_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `exp(x) = 1 + x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_rexp_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, exp x = 1 + x + E x * x ^ 2 := by
  convert taylor_rexp_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `exp(x) = 1 + x + x²/2 + x³/6 + ... + xⁿ/n! + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_rexp_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, exp x = ∑ k ∈ range (n + 1), 1 / k ! * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_rexp_bigO n)

/-- `exp(x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_rexp_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, exp x = 1 + e x := by
  convert taylor_rexp_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `exp(x) = 1 + x + o(x)` as `x ⟶ 0`. -/
theorem taylor_rexp_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, exp x = 1 + x + e x * x := by
  convert taylor_rexp_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

end taylor_rexp


section taylor_one_add_cpow
open Complex Nat

/-- `(1 + z) ^ a = 1 + a * z + ... + a(a - 1)...(a - n + 1)/n! * zⁿ + O(zⁿ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_one_add_cpow_bigO (n : ℕ) (a : ℂ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, (1 + z) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * z ^ k + E z * z ^ (n + 1) := by
  have h0 z (hz : z ∈ Metric.ball 0 1) : 1 + z ∈ slitPlane := by
    left
    simp only [add_re, one_re]
    simp at hz
    have d1 := abs_le.mp (Complex.abs_re_le_abs z)
    linarith
  have ⟨E, C, hE, h1⟩ :=
    taylor_bigO_of_series_at_zero_of_differentiableOn_ℂ (λ z ↦ (1 + z) ^ a) 1 (by norm_num) (by
      let f (z : ℂ) := (1 + z)
      let g (z : ℂ) := z ^ a
      show DifferentiableOn _ (g ∘ f) _
      apply DifferentiableOn.comp (t := slitPlane)
      . intro z hz
        exact DifferentiableWithinAt.cpow (by fun_prop) (by fun_prop) hz
      . fun_prop
      . exact h0) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, h1⟩ := h1
  rw [Metric.eventually_nhds_iff]
  use ε ⊓ 1
  use by simp [hε]
  intro z hz
  simp at hz
  specialize h1 (by simpa using hz.left)
  convert h1 using 5 with k hk
  have h1 k (z : ℂ) (hz : z ∈ Metric.ball 0 1) : (iteratedDeriv k (fun z => (1 + z) ^ a) z) = (∏ j ∈ range k, (a - j)) * (1 + z) ^ (a - k) := by
    induction' k with k ih generalizing z hz
    . simp
    . calc
        _ = deriv (λ y ↦ (iteratedDeriv k fun z => (1 + z) ^ a) y) z := by rw [iteratedDeriv_succ]
        _ = derivWithin (λ y ↦ (iteratedDeriv k fun z => (1 + z) ^ a) y) (Metric.ball 0 1) z := by
          refine Eq.symm (derivWithin_of_isOpen ?_ hz)
          exact Metric.isOpen_ball
        _ = derivWithin (λ y ↦ ((∏ j ∈ range k, (a - j)) * (1 + y) ^ (a - k))) (Metric.ball 0 1) z := by
          apply derivWithin_congr
          . intro y hy; simp [ih y hy]
          . simp [ih z hz]
        _ = deriv (λ y ↦ ((∏ j ∈ range k, (a - j)) * (1 + y) ^ (a - k))) z := by
          refine derivWithin_of_isOpen ?_ hz
          exact Metric.isOpen_ball
        _ = (∏ j ∈ range k, (a - j)) * deriv (fun x => (1 + x) ^ (a - k)) z := by simp
        _ = (∏ j ∈ range k, (a - j)) * ((a - k) * (1 + z) ^ (a - (k + 1))) := by
          congr 1
          let f (z : ℂ) := (1 + z)
          let g (z : ℂ) := z ^ (a - k)
          have d1 : 1 + z ∈ slitPlane := by
            left
            simp only [add_re, one_re]
            simp at hz
            have d1 := abs_le.mp (Complex.abs_re_le_abs z)
            linarith
          show deriv (g ∘ f) z = _
          have c1 : deriv f z = 1 := by
            rw [deriv_add]
            rw [deriv_const]
            rw [deriv_id'']
            . simp
            . fun_prop
            . fun_prop
          have c2 : deriv g (1 + z) = (a - k) * (1 + z) ^ (a - k - 1) := by
            exact (hasStrictDerivAt_cpow_const d1).hasDerivAt.deriv
          rw [deriv_comp]
          . rw [c1, c2]
            ring_nf
          . exact (hasStrictDerivAt_cpow_const d1).differentiableAt
          . fun_prop
        _ = _ := by simp [prod_range_succ]; ring
  simp [h1 k 0 (by simp)]

/-- `(1 + z) ^ a = 1 + a * z + ... + a(a - 1)...(a - n + 1)/n! * zⁿ + o(zⁿ)` as `z ⟶ 0`. -/
theorem taylor_one_add_cpow_littleO (n : ℕ) (a : ℂ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, (1 + z) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * z ^ k + e z * z ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_one_add_cpow_bigO n a)

end taylor_one_add_cpow

section taylor_one_add_rpow
open Nat

/-- `(1 + x) ^ a = 1 + a * x + ... + a(a - 1)...(a - n + 1)/n! * xⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_one_add_rpow_bigO (n : ℕ) (a : ℝ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * x ^ k + E x * x ^ (n + 1) := by
  have ⟨E, C, hE, h1⟩ := taylor_one_add_cpow_bigO n a
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ (1 + x) ^ a) (λ x ↦ ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * x ^ k) n
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε ⊓ 1, by simp [hε]
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx.left)
  convert h1 using 1
  . norm_cast
    refine Complex.ofReal_cpow ?_ a
    have hx2 := hx.right
    rw [abs_lt] at hx2
    linarith
  . norm_cast

/-- `(1 + x) ^ a = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_one_add_rpow_bigO_order0 (a : ℝ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + E x * x := by
  convert taylor_one_add_rpow_bigO 0 a using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `(1 + x) ^ a = 1 + a * x + O(x²)` as `x ⟶ 0`. -/
theorem taylor_one_add_rpow_bigO_order1 (a : ℝ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + a * x + E x * x ^ 2 := by
  convert taylor_one_add_rpow_bigO 1 a using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

/-- `(1 + x) ^ a = 1 + a * x + ... + a(a - 1)...(a - n + 1)/n! * xⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_one_add_rpow_littleO (n : ℕ) (a : ℝ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = ∑ k ∈ range (n + 1), (∏ j ∈ range k, (a - j)) / k ! * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_one_add_rpow_bigO n a)

/-- `(1 + x) ^ a = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_one_add_rpow_littleO_order0 (a : ℝ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + e x := by
  convert taylor_one_add_rpow_littleO 0 a using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `(1 + x) ^ a = 1 + a * x + o(x)` as `x ⟶ 0`. -/
theorem taylor_one_add_rpow_littleO_order1 (a : ℝ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, (1 + x) ^ a = 1 + a * x + e x * x := by
  convert taylor_one_add_rpow_littleO 1 a using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  simp [h1]

end taylor_one_add_rpow

section taylor_sqrt_one_add
open Real Nat

/-- `√(1 + x) = 1 + x/2 - x²/8 + ... + (1/2)(1/2 - 1)...(1/2 - n + 1)/n! * xⁿ + O(xⁿ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_bigO (n : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, √(1 + x) = ∑ k ∈ range (n + 1), (∏ j ∈ range k, ((1 : ℝ) / 2 - j)) / k ! * x ^ k + E x * x ^ (n + 1) := by
  convert taylor_one_add_rpow_bigO n (1 / 2) using 9 with E C hE x
  apply sqrt_eq_rpow

/-- `√(1 + x) = 1 + O(x)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_bigO_order0 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + E x * x := by
  convert taylor_sqrt_one_add_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `√(1 + x) = 1 + x/2 + O(x²)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + x / 2 + E x * x ^ 2 := by
  convert taylor_sqrt_one_add_bigO 1 using 9 with E C hE x
  have h1 : range 2 = {0, 1} := by decide
  field_simp [h1]

/-- `√(1 + x) = 1 + x/2 - x²/8 + ... + (1/2)(1/2 - 1)...(1/2 - n + 1)/n! * xⁿ + o(xⁿ)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_littleO (n : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, √(1 + x) = ∑ k ∈ range (n + 1), (∏ j ∈ range k, ((1 : ℝ) / 2 - j)) / k ! * x ^ k + e x * x ^ n := by
  exact taylor_littleO_of_bigO_at_zero (taylor_sqrt_one_add_bigO n)

/-- `√(1 + x) = 1 + o(1)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_littleO_order0 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + e x := by
  convert taylor_sqrt_one_add_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `√(1 + x) = 1 + x/2 + o(x)` as `x ⟶ 0`. -/
theorem taylor_sqrt_one_add_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, √(1 + x) = 1 + x / 2 + e x * x := by
  convert taylor_sqrt_one_add_littleO 1 using 7 with e he x
  have h1 : range 2 = {0, 1} := by decide
  field_simp [h1]

end taylor_sqrt_one_add

section taylor_ccos
open Complex Nat

/-- `cos(z) = 1 - z²/2 + ... + (-1)ᵐ z²ᵐ/(2m)! + O(z²ᵐ⁺²)` as `z ⟶ 0`. -/
theorem taylor_ccos_bigO (m : ℕ) :
    ∃ (E : ℂ → ℂ), ∃ (C : ℝ) (_ : ∀ᶠ z in 𝓝 0, ‖E z‖ ≤ C),
    ∀ᶠ z in 𝓝 0, cos z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * z ^ (2 * k) + E z * z ^ (2 * m + 2) := by
  -- TODO: use `Complex.hasSum_cos` instead of reproving the formula
  convert taylor_bigO_of_series_at_zero_of_differentiableOn_ℂ cos 1 (by norm_num)
    differentiable_cos.differentiableOn (2 * m + 1) using 10 with E C hE z
  have h1 : range (2 * m + 1 + 1) = (range (m + 1)).biUnion (λ k ↦ {2 * k, 2 * k + 1}) := by
    ext k
    constructor <;> intro hk <;> simp at hk ⊢
    . use k / 2; omega
    . omega
  rw [h1, sum_biUnion]
  swap
  . intro i hi j hj hij s hsi hsj x hx
    specialize hsi hx
    specialize hsj hx
    simp at hsi hsj
    omega
  apply sum_congr rfl
  intro k hk
  rw [sum_pair (by omega)]
  calc
    _ = (-1) ^ k / (2 * k) ! * z ^ (2 * k) + 0 / (2 * k + 1) ! * z ^ (2 * k + 1) := by simp
    _ = _ := by
      have c1 k : iteratedDeriv (2 * k) cos 0 = (-1) ^ k ∧ iteratedDeriv (2 * k + 1) cos 0 = 0 := by
        induction' k with k ih
        . simp
        . constructor
          . calc
              _ = iteratedDeriv (2 * k + 2) cos 0 := by ring_nf
              _ = -iteratedDeriv (2 * k) cos 0 := by simp [iteratedDeriv_succ', iteratedDeriv_neg]
              _ = _ := by rw [ih.left]; ring
          . calc
              _ = iteratedDeriv (2 * k + 3) cos 0 := by ring_nf
              _ = -iteratedDeriv (2 * k + 1) cos 0 := by simp [iteratedDeriv_succ', iteratedDeriv_neg]
              _ = _ := by rw [ih.right]; ring
      symm
      congr 3
      . exact (c1 k).left
      . exact (c1 k).right

/-- `cos(z) = 1 - z²/2 + ... + (-1)ᵐ z²ᵐ/(2m)! + o(z²ᵐ⁺¹)` as `z ⟶ 0`. -/
theorem taylor_ccos_littleO (m : ℕ) :
    ∃ (e : ℂ → ℂ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ z in 𝓝 0, cos z = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * z ^ (2 * k) + e z * z ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_ccos_bigO m)

end taylor_ccos

section taylor_rcos
open Real Nat

/-- `cos(x) = 1 - x²/2 + ... + (-1)ᵐ x²ᵐ/(2m)! + O(x²ᵐ⁺²)` as `x ⟶ 0`. -/
theorem taylor_rcos_bigO (m : ℕ) :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, cos x = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * x ^ (2 * k) + E x * x ^ (2 * m + 2) := by
  have ⟨E, C, hE, h1⟩ := taylor_ccos_bigO m
  apply taylor_bigO_at_zero_ℝ_of_ℂ
    (λ x ↦ cos x) (λ x ↦ ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * x ^ (2 * k)) (2 * m + 1)
  use E, C, hE
  rw [Metric.eventually_nhds_iff] at h1 ⊢
  obtain ⟨ε, hε, h1⟩ := h1
  use ε, hε
  intro x hx
  simp at hx
  specialize h1 (y := x) (by simpa using hx)
  convert h1 using 1
  . simp
  . norm_cast

/-- `cos(x) = 1 + O(x²)` as `x ⟶ 0`. -/
theorem taylor_rcos_bigO_order1 :
    ∃ (E : ℝ → ℝ), ∃ (C : ℝ) (_ : ∀ᶠ x in 𝓝 0, ‖E x‖ ≤ C),
    ∀ᶠ x in 𝓝 0, cos x = 1 + E x * x ^ 2 := by
  convert taylor_rcos_bigO 0 using 9 with E C hE x
  have h1 : range 1 = {0} := by decide
  simp [h1]

/-- `cos(x) = 1 - x²/2 + ... + (-1)ᵐ x²ᵐ/(2m)! + o(x²ᵐ⁺¹)` as `x ⟶ 0`. -/
theorem taylor_rcos_littleO (m : ℕ) :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, cos x = ∑ k ∈ range (m + 1), (-1) ^ k / (2 * k) ! * x ^ (2 * k) + e x * x ^ (2 * m + 1) := by
  exact taylor_littleO_of_bigO_at_zero (taylor_rcos_bigO m)

/-- `cos(x) = 1 + o(x)` as `x ⟶ 0`. -/
theorem taylor_rcos_littleO_order1 :
    ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
    ∀ᶠ x in 𝓝 0, cos x = 1 + e x * x := by
  convert taylor_rcos_littleO 0 using 7 with e he x
  have h1 : range 1 = {0} := by decide
  simp [h1]

end taylor_rcos


-- Add other trigonometric and hyperbolic functions


open Real in
/-- (1 + 1/n)^n ⟶ e -/
example : Tendsto (λ n : ℕ ↦ (1 + (1 : ℝ) / n) ^ n) atTop (𝓝 (exp 1)) := by
  suffices ∃ (e : ℝ → ℝ) (_ : Tendsto e (𝓝 0) (𝓝 0)),
      ∀ᶠ x in 𝓝[≠] 0, (1 + x) ^ (1 / x) = exp 1 + e x by
    obtain ⟨e, he, h1⟩ := this
    let f (n : ℕ) := exp 1 + e (1 / n)
    have h2 : Tendsto f atTop (𝓝 (exp 1)) := by
      suffices Tendsto f atTop (𝓝 (exp 1 + 0)) from by convert this using 2; simp
      apply Tendsto.add
      . exact tendsto_const_nhds
      . show Tendsto (e ∘ λ n : ℕ ↦ 1 / n) atTop (𝓝 0)
        apply Tendsto.comp he
        exact tendsto_one_div_atTop_nhds_zero_nat
    convert h2 using 0
    apply Iff.symm (tendsto_congr' ?_)
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at h1
    obtain ⟨ε, hε, h1⟩ := h1
    rw [EventuallyEq, eventually_atTop]
    use Nat.ceil (1 / ε + 1)
    intro k hk
    replace hk : k ≥ 1 / ε + 1 := Nat.le_of_ceil_le hk
    have hε' : 1 / ε > 0 := by positivity
    have hk' : (k : ℝ) > 0 := by linarith
    replace hk : k > 1 / ε := by linarith
    replace hk : (1 : ℝ) / k < ε := by refine (one_div_lt hε hk').mp hk
    have h3 : (1 : ℝ) / k ∈ Metric.ball 0 ε ∩ {0}ᶜ := by
      constructor
      . simpa using hk
      . norm_cast at hk'; simp; omega
    specialize h1 h3
    dsimp at h1
    symm
    convert h1 using 3
    calc
      ((1 : ℝ) + 1 / k) ^ k = (1 + 1 / k) ^ (k : ℝ) := by norm_cast
      _ = _ := by congr 1; simp


-- (1 + x) ^ (1 / x) = exp ((1 / x) * log (1 + x)) = exp ((1 / x) * (x + o(x)))
-- = exp (1 + o(1)) = exp 1 * exp (o(1)) = exp 1 * (1 + o(1)) = exp 1 + o(1)
  have ⟨e1, he1, h1⟩ := taylor_rlog_one_add_littleO_order1
  have ⟨e2, he2, h2⟩ := taylor_rexp_littleO_order0
  replace h2 := he1.eventually h2
  use λ x ↦ exp 1 * e2 (e1 x)
  use by
    convert_to Tendsto (λ x ↦ rexp 1 * e2 (e1 x)) (𝓝 0) (𝓝 (rexp 1 * 0)) using 2
    . ring
    apply Tendsto.const_mul
    apply he2.comp he1
  rw [Metric.eventually_nhds_iff] at h1 h2
  obtain ⟨ε1, hε1, h1⟩ := h1
  obtain ⟨ε2, hε2, h2⟩ := h2
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
  use ε1 ⊓ ε2 ⊓ 1, by simp [hε1, hε2]
  intro x ⟨hx1, hx2⟩
  simp only [Metric.mem_ball, lt_inf_iff] at hx1
  simp at hx2
  specialize h1 hx1.left.left
  specialize h2 hx1.left.right
  calc
    (1 + x) ^ (1 / x) = exp (log (1 + x) * (1 / x)) := by
      refine rpow_def_of_pos ?_ (1 / x)
      replace hx1 := hx1.right
      simp [abs_lt] at hx1
      linarith
    _ = exp (1 / x * log (1 + x)) := by ring_nf
    _ = exp (1 / x * (x + e1 x * x)) := by simp [h1]
    _ = exp (1 + e1 x) := by
      congr 1
      field_simp
      ring
    _ = exp 1 * exp (e1 x) := by apply exp_add
    _ = exp 1 * (1 + e2 (e1 x)) := by rw [h2]
    _ = _ := by ring
