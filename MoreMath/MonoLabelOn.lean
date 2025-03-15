import Mathlib


open Finset

-- API to talk about the argmin over a Finset

noncomputable def argmin {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) : α :=
  have h := (image f s).isLeast_min' (by simp [H])
  (Finset.mem_image.mp h.1).choose

theorem argmin_mem {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
    argmin f s H ∈ s := by
  have h := (image f s).isLeast_min' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.1

theorem apply_argmin {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
    f (argmin f s H) = (s.image f).min' (by simp [H]) := by
  have h := (image f s).isLeast_min' (by simp [H])
  exact (Finset.mem_image.mp h.1).choose_spec.2

theorem le_argmin {α β : Type _} [LinearOrder β] (f : α → β) (s : Finset α) (H : s.Nonempty) :
    ∀ a ∈ s, f (argmin f s H) ≤ f a := by
  have h := (image f s).isLeast_min' (by simp [H])
  simpa [lowerBounds, apply_argmin f s H] using h.2


-- monoLabelOn API

-- if (x_i) is indexed over a set s,
-- then φ = monoLabelOn x s i0 provides a sorted reindexing of x from {i0, i0+1,...,i0+#s} to x(s).

-- image_comp_monoLabelOn says that (x_{φ_i}) i.e. x ∘ φ  will map {i0, i0+1,...,i0+#s} to x(s)

-- monotoneOn_comp_monoLabelOn says that x_{φ_1} ≤ x_{φ_2} ≤ ... ≤ x_{φ_{#s}}

-- bijOn_monoLabelOn says that φ : {i0, i0+1,...,i0+#s} → s is bijective.

-- Additionally if x is injective, strictMonoOn_comp_monoLabelOn_of_injOn says that
-- the ordering is strict x_{φ_1} < x_{φ_2} < ... < x_{φ_{#s}}

-- monoLabelOn gives rise to monoLabel which uses x = identity
-- which thereby provides a strict mono indexing of the elements of a set



-- The idea to construct φ is to pick the index i of the smallest x_i
--    then pick the index i of the next smallest x_i, etc...
-- So φ(i0+n) is defined as the index of the (n+1)th-smallest x_i in s
-- i.e. the index of the smallest x_i in s \ {n previous answers}

noncomputable def monoLabelOn
    {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
    (x : ι → α) (s : Finset ι) (i0 : ℕ) : ℕ → ι :=
  Nat.lt_wfRel.wf.fix (λ n ih ↦
    if hn : n ∈ Ico i0 (i0 + #s) then
    let label_lt_n k := if hk : k < n then ih k hk else 0
    argmin x (s \ (Ico i0 n).image label_lt_n) (by
      apply nonempty_of_ne_empty
      intro h1
      apply_fun (#.) at h1
      conv_rhs at h1 => simp
      have c1 := le_card_sdiff ((Ico i0 n).image label_lt_n) s
      have c2 : #((Ico i0 n).image label_lt_n) ≤ _ := card_image_le
      simp at c2
      simp at hn
      omega)
    else 0)

theorem nonempty_sdiff_Ico_of_lt_card
    {ι : Type _} [Zero ι] [DecidableEq ι]
    (y : ℕ → ι) {s : Finset ι} {i0 : ℕ} {n : ℕ} (hn : n ∈ Ico i0 (i0 + #s))
    : (s \ (Ico i0 n).image y).Nonempty := by
  apply nonempty_of_ne_empty
  intro h1
  apply_fun (#.) at h1
  conv_rhs at h1 => simp
  have c1 := le_card_sdiff ((Ico i0 n).image y) s
  have c2 : #((Ico i0 n).image y) ≤ _ := card_image_le
  simp at c2
  simp at hn
  omega


-- The main recursive equation satisfied by monoLabelOn
theorem monoLabelOn_eq
    {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
    (x : ι → α) (s : Finset ι) (i0 : ℕ) (n : ℕ) (hn : n ∈ Ico i0 (i0 + #s)) :
    monoLabelOn x s i0 n =
      argmin x (s \ (Ico i0 n).image (monoLabelOn x s i0))
        (nonempty_sdiff_Ico_of_lt_card _ hn) := by
    dsimp only [monoLabelOn]
    conv_lhs => rw [Nat.lt_wfRel.wf.fix_eq]
    split_ifs
    symm
    have h0 := nonempty_sdiff_Ico_of_lt_card (monoLabelOn x s i0) hn
    congr 2
    ext k
    simp only [mem_image, mem_Ico]
    constructor <;> intro ⟨l, h1, h2⟩
    . use l, h1
      simpa [h1.right] using h2
    . simp [h1.right] at h2
      use l

theorem bijOn_monoLabelOn
    {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
    (x : ι → α) (s : Finset ι) (i0 : ℕ) : Set.BijOn (monoLabelOn x s i0) (Ico i0 (i0 + #s)) s := by
  have a1 : Set.MapsTo (monoLabelOn x s i0) (Ico i0 (i0 + #s)) s := by
    intro n hn
    have h1 : monoLabelOn x s i0 n ∈ s \ (Ico i0 n).image (monoLabelOn x s i0) := by
      rw [monoLabelOn_eq x s i0 n hn]
      apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hn)
    rw [mem_sdiff] at h1
    exact h1.left
  have a2 : Set.InjOn (monoLabelOn x s i0) (Ico i0 (i0 + #s)) := by
    intro i hi j hj hij
    let m := monoLabelOn x s i0 i
    have h1 : m ∈ s \ (Ico i0 i).image (monoLabelOn x s i0) := by
      dsimp [m]
      rw [monoLabelOn_eq x s i0 i hi]
      apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hi)
    have h2 : m ∈ s \ (Ico i0 j).image (monoLabelOn x s i0) := by
      dsimp [m]
      rw [hij]
      rw [monoLabelOn_eq x s i0 j hj]
      apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hj)
    rw [mem_sdiff] at h1 h2
    replace h1 := h1.right
    replace h2 := h2.right
    simp at h1 h2
    simp at hi hj
    have h3 : ¬i < j := by
      intro h3
      apply h2 i (by omega) h3
      rfl
    have h4 : ¬j < i := by
      intro h4
      apply h1 j (by omega) h4
      exact hij.symm
    omega
  have a3 : Set.SurjOn (monoLabelOn x s i0) (Ico i0 (i0 + #s)) s := by
    have h1 := Set.surjOn_image (monoLabelOn x s i0) (Ico i0 (i0 + #s))
    suffices (monoLabelOn x s i0) '' (Ico i0 (i0 + #s)) = s from by rwa [this] at h1
    rw [←coe_image]
    apply congrArg Finset.toSet
    apply eq_of_subset_of_card_le
    . intro y hy
      obtain ⟨k, hk, hk2⟩ := by simpa only [mem_image] using hy
      subst hk2
      exact a1 hk
    . simp [card_image_of_injOn a2]
  split_ands
  . exact a1
  . exact a2
  . exact a3

theorem image_comp_monoLabelOn
    {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
    (x : ι → α) (s : Finset ι) (i0 : ℕ) : (Ico i0 (i0 + #s)).image (x ∘ monoLabelOn x s i0) = s.image x := by
  apply coe_inj.mp
  simp only [coe_image, Set.image_comp]
  apply congrArg (x '' .)
  exact (bijOn_monoLabelOn x s i0).image_eq

theorem monotoneOn_comp_monoLabelOn
    {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
    (x : ι → α) (s : Finset ι) (i0 : ℕ) : MonotoneOn (x ∘ monoLabelOn x s i0) (Ico i0 (i0 + #s)) := by
  intro i hi j hj hij
  dsimp
  rw [monoLabelOn_eq x s i0 i hi]
  rw [monoLabelOn_eq x s i0 j hj]
  apply le_argmin x _ (nonempty_sdiff_Ico_of_lt_card _ hi)
  suffices s \ (Ico i0 j).image (monoLabelOn x s i0) ⊆ s \ (Ico i0 i).image (monoLabelOn x s i0) from by
    apply this
    apply argmin_mem x _ (nonempty_sdiff_Ico_of_lt_card _ hj)
  apply sdiff_subset_sdiff (by simp)
  apply image_subset_image
  intro k
  simp
  omega

theorem strictMonoOn_comp_monoLabelOn_of_injOn
    {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
    (x : ι → α) (s : Finset ι) (i0 : ℕ) (h0 : Set.InjOn x s)
    : StrictMonoOn (x ∘ monoLabelOn x s i0) (Ico i0 (i0 + #s)) := by
  have h1 := monotoneOn_comp_monoLabelOn x s i0
  have h2 : Set.InjOn (x ∘ monoLabelOn x s i0) (Ico i0 (i0 + #s)) := by
    have c1 := bijOn_monoLabelOn x s i0
    have c2 := c1.injOn
    intro i hi j hj hij
    specialize h0 (c1.mapsTo hi) (c1.mapsTo hj) hij
    exact c2 hi hj h0
  intro i hi j hj hij
  apply lt_of_le_of_ne
  . apply h1 hi hj (by omega)
  . intro c1
    specialize h2 hi hj c1
    omega

-- this is the inverse map, mapping an s-index back to {i0, i0+1,...,i0+#s}
noncomputable def invMonoLabelOn
    {α ι : Type _} [Zero α] [LinearOrder α] [Zero ι] [DecidableEq ι]
    (x : ι → α) (s : Finset ι) (i0 : ℕ) : ι → ℕ := (monoLabelOn x s i0).invFunOn (Ico i0 (i0 + #s))



-- monoLabel is a special case, and indexes elements of a set starting at i0

noncomputable def monoLabel
    {α : Type _} [Zero α] [LinearOrder α]
    (s : Finset α) (i0 : ℕ) : ℕ → α := monoLabelOn id s i0

theorem image_monoLabel
    {α : Type _} [Zero α] [LinearOrder α]
    (s : Finset α) i0 : (Ico i0 (i0 + #s)).image (monoLabel s i0) = s := by
  simpa using image_comp_monoLabelOn id s i0

theorem strictMonoOn_monoLabel
    {α : Type _} [Zero α] [LinearOrder α]
    (s : Finset α) i0 : StrictMonoOn (monoLabel s i0) (Ico i0 (i0 + #s)) := by
  simpa using strictMonoOn_comp_monoLabelOn_of_injOn id s i0  (by apply Set.injOn_id)

theorem bijOn_monoLabel
    {α : Type _} [Zero α] [LinearOrder α]
    (s : Finset α) i0 : Set.BijOn (monoLabel s i0) (Ico i0 (i0 + #s)) s := by
  simpa using bijOn_monoLabelOn id s i0
