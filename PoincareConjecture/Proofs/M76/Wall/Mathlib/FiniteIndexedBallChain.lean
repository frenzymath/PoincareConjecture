import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteBallChain










set_option autoImplicit false

open Set

namespace Set





theorem isFinitePLBallPair_fin_ball_chain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (B T : Fin (n + 2) → Set E) (J Q : Fin (n + 1) → Set E)
    {F₀ F₁ : Set E}
    (hB : ∀ i, IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B i) (T i))
    (hJ : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (J i) (Q i))
    (hcontact : ∀ i, B i.castSucc ∩ B i.succ = J i)
    (hboundary : ∀ i, J i ⊆ T i.castSucc ∧ J i ⊆ T i.succ)
    (hfar : ∀ i j, i.val + 1 < j.val → Disjoint (B i) (B j))
    (hjoints : ∀ i j, i ≠ j → Disjoint (J i) (J j))
    (hF₀ : F₀ ⊆ T 0) (hF₁ : F₁ ⊆ T (Fin.last (n + 1)))
    (hne₀ : F₀.Nonempty) (hne₁ : F₁.Nonempty)
    (havoid : ∀ i, Disjoint F₀ (J i) ∧ Disjoint F₁ (J i)) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (⋃ i, B i)
        ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
      F₀ ⊆ ((⋃ i, T i) \ ⋃ i, J i \ Q i) ∧
      F₁ ⊆ ((⋃ i, T i) \ ⋃ i, J i \ Q i) := by
  let b : ℕ → Set E := fun i => if hi : i < n + 2 then B ⟨i, hi⟩ else ∅
  let t : ℕ → Set E := fun i => if hi : i < n + 2 then T ⟨i, hi⟩ else ∅
  let j : ℕ → Set E := fun i => if hi : i < n + 1 then J ⟨i, hi⟩ else ∅
  let q : ℕ → Set E := fun i => if hi : i < n + 1 then Q ⟨i, hi⟩ else ∅
  have hb (i : ℕ) (hi : i < n + 2) : b i = B ⟨i, hi⟩ := dif_pos hi
  have ht (i : ℕ) (hi : i < n + 2) : t i = T ⟨i, hi⟩ := dif_pos hi
  have hj (i : ℕ) (hi : i < n + 1) : j i = J ⟨i, hi⟩ := dif_pos hi
  have hq (i : ℕ) (hi : i < n + 1) : q i = Q ⟨i, hi⟩ := dif_pos hi
  have hballs (i : ℕ) (hi : i ≤ n + 1) :
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (b i) (t i) := by
    rw [hb i (by omega), ht i (by omega)]
    exact hB _
  have hdisks (i : ℕ) (hi : i < n + 1) :
      IsFinitePLBallPair (ℝ × ℝ) (j i) (q i) := by
    rw [hj i hi, hq i hi]
    exact hJ _
  have hcontacts (i : ℕ) (hi : i < n + 1) : b i ∩ b (i + 1) = j i := by
    rw [hb i (by omega), hb (i + 1) (by omega), hj i hi]
    exact hcontact ⟨i, hi⟩
  have hboundaries (i : ℕ) (hi : i < n + 1) :
      j i ⊆ t i ∧ j i ⊆ t (i + 1) := by
    rw [hj i hi, ht i (by omega), ht (i + 1) (by omega)]
    exact hboundary ⟨i, hi⟩
  have hfar' (i : ℕ) (hi : i ≤ n + 1) (k : ℕ) (hk : k ≤ n + 1)
      (hik : i + 1 < k) : Disjoint (b i) (b k) := by
    rw [hb i (by omega), hb k (by omega)]
    exact hfar _ _ hik
  have hjoints' (i : ℕ) (hi : i < n + 1) (k : ℕ) (hk : k < n + 1)
      (hik : i ≠ k) : Disjoint (j i) (j k) := by
    rw [hj i hi, hj k hk]
    exact hjoints _ _ (fun he => hik (congrArg Fin.val he))
  have hfirst : F₀ ⊆ t 0 := by
    rw [ht 0 (by omega)]
    exact hF₀
  have hlast : F₁ ⊆ t (n + 1) := by
    rw [ht (n + 1) (by omega)]
    exact hF₁
  have havoid' (i : ℕ) (hi : i < n + 1) :
      Disjoint F₀ (j i) ∧ Disjoint F₁ (j i) := by
    rw [hj i hi]
    exact havoid _
  have hball := isFinitePLBallPair_finite_ball_chain b t j q (n + 1)
    hballs hdisks hcontacts hboundaries hfar' hjoints'
    hfirst hlast hne₀ hne₁ havoid'
  have hBunion : (⋃ i ≤ n + 1, b i) = ⋃ i, B i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      rw [hb i (by omega)] at hxi
      exact mem_iUnion.mpr ⟨⟨i, by omega⟩, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      refine mem_iUnion₂.mpr ⟨i.val, by omega, ?_⟩
      rwa [hb i.val i.isLt]
  have hTunion : (⋃ i ≤ n + 1, t i) = ⋃ i, T i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      rw [ht i (by omega)] at hxi
      exact mem_iUnion.mpr ⟨⟨i, by omega⟩, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      refine mem_iUnion₂.mpr ⟨i.val, by omega, ?_⟩
      rwa [ht i.val i.isLt]
  have hJunion : (⋃ i < n + 1, j i \ q i) = ⋃ i, J i \ Q i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      rw [hj i hi, hq i hi] at hxi
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      refine mem_iUnion₂.mpr ⟨i.val, i.isLt, ?_⟩
      rwa [hj i.val i.isLt, hq i.val i.isLt]
  simpa only [hBunion, hTunion, hJunion] using hball

end Set
