import PoincareConjecture.Proofs.M76.Mathlib.OrdinaryCapHeightSigns











set_option autoImplicit false

open Set

namespace Set

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ E] in



theorem mem_closure_height_lt_of_ball_sublevel
    {D : Set E} (A : E → ℝ) {c : ℝ}
    (hD : IsFinitePLBallPair V (D ∩ {x | A x ≤ c}) (D ∩ {x | A x = c}))
    {x : E} (hx : x ∈ D ∩ {x | A x = c}) :
    x ∈ closure (D ∩ {y | A y < c}) := by
  have hdiff : (D ∩ {y | A y ≤ c}) \ (D ∩ {y | A y = c}) =
      D ∩ {y | A y < c} := by
    ext y
    constructor
    · rintro ⟨⟨hy, hle⟩, hn⟩
      exact ⟨hy, lt_of_le_of_ne hle (fun heq => hn ⟨hy, heq⟩)⟩
    · rintro ⟨hy, hlt⟩
      change A y < c at hlt
      exact ⟨⟨hy, hlt.le⟩, fun heq => hlt.ne heq.2⟩
  have h := hD.closure_sdiff
  rw [hdiff] at h
  exact h.symm ▸ hD.1 hx




theorem IsFinitePLBallPair.rim_eq_top_of_ball_sublevel
    {D B : Set E} (hD : IsFinitePLBallPair V D B)
    (A : E → ℝ) {t : ℝ}
    (hupper : ∀ x ∈ D, A x ≤ t)
    (htop : IsFinitePLBallPair V (D ∩ {x | A x ≤ t}) (D ∩ {x | A x = t})) :
    B = D ∩ {x | A x = t} := by
  have hcarrier : D ∩ {x | A x ≤ t} = D :=
    inter_eq_left.mpr hupper
  rw [hcarrier] at htop
  exact hD.boundary_eq_of_same_carrier htop





theorem ordinary_cap_mem_both_height_closures_of_rim_approach
    {D B S : Set E} (A : E → ℝ) {t : ℝ} (ht : 0 < t)
    (hD : IsFinitePLBallPair V D B) (hDS : D ⊆ S)
    (hempty : ∀ c : ℝ, c < t * (2 / 3) ∨ t < c → D ∩ {x | A x = c} = ∅)
    (hlevels : ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
      IsFinitePLBallPair V (D ∩ {x | A x ≤ t * a}) (D ∩ {x | A x = t * a}))
    (hrim : ∀ x ∈ B, x ∈ closure (S ∩ {y | t < A y}))
    {x : E} (hx : x ∈ D) (hne : A x ≠ t * (2 / 3)) :
    x ∈ closure (S ∩ {y | A y < A x}) ∧
      x ∈ closure (S ∩ {y | A x < A y}) := by
  have hupper (y : E) (hy : y ∈ D) : A y ≤ t := by
    by_contra hn
    have hf : y ∈ D ∩ {z | A z = A y} := ⟨hy, rfl⟩
    rw [hempty (A y) (Or.inr (lt_of_not_ge hn))] at hf
    exact hf
  have hlower : t * (2 / 3) < A x := by
    apply lt_of_le_of_ne _ hne.symm
    by_contra hn
    have hf : x ∈ D ∩ {y | A y = A x} := ⟨hx, rfl⟩
    rw [hempty (A x) (Or.inl (lt_of_not_ge hn))] at hf
    exact hf
  by_cases hxt : A x < t
  · obtain ⟨hlo, hhi⟩ := ordinary_cap_mem_both_height_closures A ht hlevels
      ⟨hlower, hxt⟩ ⟨hx, rfl⟩
    exact ⟨closure_mono (inter_subset_inter_left _ hDS) hlo,
      closure_mono (inter_subset_inter_left _ hDS) hhi⟩
  · have heq : A x = t := le_antisymm (hupper x hx) (le_of_not_gt hxt)
    have htop := hlevels 1 ⟨by norm_num, le_rfl⟩
    simp only [mul_one] at htop
    have hxb : x ∈ B := by
      rw [hD.rim_eq_top_of_ball_sublevel A hupper htop]
      exact ⟨hx, heq⟩
    rw [heq]
    exact ⟨closure_mono (inter_subset_inter_left _ hDS)
      (mem_closure_height_lt_of_ball_sublevel A htop ⟨hx, heq⟩), hrim x hxb⟩

end Set
