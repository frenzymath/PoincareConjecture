import PoincareConjecture.Proofs.M76.Mathlib.TriangularPLCornerLevels
import PoincareConjecture.Proofs.M76.Triangulation.AffineConvexSphereCapDisks










set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

private theorem weighted_height_interior_section {m₁ m₂ c : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hc : c ∈ Ioo 0 (min m₁ m₂)) :
    ∃ p ∈ interior base, m₁ * p.1 + m₂ * p.2 = c := by
  let x := c / (m₁ + m₂)
  have hs : 0 < m₁ + m₂ := add_pos hm₁ hm₂
  have hx : 0 < x := div_pos hc.1 hs
  have hsum : x + x < 1 := by
    dsimp [x]
    rw [← add_div, div_lt_one hs]
    have hcm₁ := hc.2.trans_le (min_le_left _ _)
    have hcm₂ := hc.2.trans_le (min_le_right _ _)
    linarith
  refine ⟨(x, x), ?_, ?_⟩
  · rw [interior_base]
    change 0 < min x (min x (1 - x - x))
    exact lt_min hx (lt_min hx (by linarith))
  · change m₁ * x + m₂ * x = c
    dsimp [x]
    field_simp [hs.ne']





theorem isFinitePLBallPair_weighted_corner_rim_caps {m₁ m₂ c : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hc : c ∈ Ioo 0 (min m₁ m₂)) :
    IsFinitePLBallPair ℝ (frontier base ∩ {p | m₁ * p.1 + m₂ * p.2 ≤ c})
      (frontier base ∩ {p | m₁ * p.1 + m₂ * p.2 = c}) ∧
    IsFinitePLBallPair ℝ (frontier base ∩ {p | c ≤ m₁ * p.1 + m₂ * p.2})
      (frontier base ∩ {p | m₁ * p.1 + m₂ * p.2 = c}) := by
  obtain ⟨p, hp, hpc⟩ := weighted_height_interior_section hm₁ hm₂ hc
  obtain ⟨l, hl, hlc⟩ := weighted_height_interior_section hm₁ hm₂
    (show c / 2 ∈ Ioo 0 (min m₁ m₂) from
      ⟨half_pos hc.1, (half_lt_self hc.1).trans hc.2⟩)
  obtain ⟨u, hu, huc⟩ := weighted_height_interior_section hm₁ hm₂
    (show (c + min m₁ m₂) / 2 ∈ Ioo 0 (min m₁ m₂) from
      ⟨half_pos (add_pos hc.1 (lt_min hm₁ hm₂)), by linarith [hc.2]⟩)
  let L := m₁ • LinearMap.fst ℝ ℝ ℝ + m₂ • LinearMap.snd ℝ ℝ ℝ
  let A : (ℝ × ℝ) →ᵃ[ℝ] ℝ := L.toAffineMap - AffineMap.const ℝ (ℝ × ℝ) c
  have hAp : A p = 0 := sub_eq_zero.mpr hpc
  have hAl : A l < 0 := by change m₁ * l.1 + m₂ * l.2 - c < 0; rw [hlc]; linarith [hc.1]
  have hAu : 0 < A u := by
    change 0 < m₁ * u.1 + m₂ * u.2 - c
    rw [huc]
    linarith [hc.2]
  have hcopy := isFinitePLBallPair_base
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hcopy
  have hcv : Convex ℝ base := by rw [base_eq_triangle]; exact convex_convexHull ℝ _
  have hhigh := K.isFinitePLBallPair_convex_frontier_affine_cap (F := ℝ) hK
    isCompact_base hcv hspace A ⟨l, hl, hAl⟩ ⟨p, hp, hAp⟩ (by simp)
  have hlow := K.isFinitePLBallPair_convex_frontier_affine_cap (F := ℝ) hK
    isCompact_base hcv hspace (-A) ⟨u, hu, neg_neg_of_pos hAu⟩
      ⟨p, hp, by change -A p = 0; rw [hAp, neg_zero]⟩ (by simp)
  have hlowset : {p | 0 ≤ (-A) p} = {p | m₁ * p.1 + m₂ * p.2 ≤ c} := by
    ext p
    change 0 ≤ -(m₁ * p.1 + m₂ * p.2 - c) ↔ m₁ * p.1 + m₂ * p.2 ≤ c
    constructor <;> intro h <;> linarith
  have hhighset : {p | 0 ≤ A p} = {p | c ≤ m₁ * p.1 + m₂ * p.2} := by
    ext p
    change 0 ≤ m₁ * p.1 + m₂ * p.2 - c ↔ c ≤ m₁ * p.1 + m₂ * p.2
    exact sub_nonneg
  have hzeroset : {p | A p = 0} = {p | m₁ * p.1 + m₂ * p.2 = c} := by
    ext p
    change m₁ * p.1 + m₂ * p.2 - c = 0 ↔ m₁ * p.1 + m₂ * p.2 = c
    exact sub_eq_zero
  have hnegzeroset : {p | (-A) p = 0} = {p | A p = 0} := by
    ext p
    exact neg_eq_zero
  rw [hlowset, hnegzeroset, hzeroset] at hlow
  rw [hhighset, hzeroset] at hhigh
  exact ⟨hlow, hhigh⟩





theorem exists_small_corner_rim_intervals {f : (ℝ × ℝ) → ℝ}
    (hf : FinitePiecewiseAffineOn f (frontier base)) (hzero : f (0, 0) = 0)
    (hpos : ∀ p ∈ frontier base, p ≠ (0, 0) → 0 < f p) :
    ∃ η : ℝ, 0 < η ∧ ∀ c ∈ Ioo 0 η,
      IsFinitePLBallPair ℝ (frontier base ∩ {p | f p ≤ c})
        (frontier base ∩ {p | f p = c}) ∧
      IsFinitePLBallPair ℝ (frontier base ∩ {p | c ≤ f p})
        (frontier base ∩ {p | f p = c}) := by
  obtain ⟨m₁, m₂, η, hm₁, hm₂, hη, hηtop, hcmp⟩ :=
    exists_small_corner_level_comparisons hf hzero hpos
  refine ⟨η, hη, fun c hc => ?_⟩
  have hsub : frontier base ∩ {p | f p ≤ c} =
      frontier base ∩ {p | m₁ * p.1 + m₂ * p.2 ≤ c} := by
    ext p
    by_cases hp : p ∈ frontier base
    · simp only [mem_inter_iff, mem_ofPred_eq, hp, true_and]
      exact (hcmp c ⟨hc.1.le, hc.2.le⟩ p hp).1
    · simp only [mem_inter_iff, hp, false_and]
  have hlevel : frontier base ∩ {p | f p = c} =
      frontier base ∩ {p | m₁ * p.1 + m₂ * p.2 = c} := by
    ext p
    by_cases hp : p ∈ frontier base
    · simp only [mem_inter_iff, mem_ofPred_eq, hp, true_and]
      exact (hcmp c ⟨hc.1.le, hc.2.le⟩ p hp).2.1
    · simp only [mem_inter_iff, hp, false_and]
  have hsuper : frontier base ∩ {p | c ≤ f p} =
      frontier base ∩ {p | c ≤ m₁ * p.1 + m₂ * p.2} := by
    ext p
    by_cases hp : p ∈ frontier base
    · simp only [mem_inter_iff, mem_ofPred_eq, hp, true_and]
      exact (hcmp c ⟨hc.1.le, hc.2.le⟩ p hp).2.2
    · simp only [mem_inter_iff, hp, false_and]
  rw [hsub, hlevel, hsuper]
  exact isFinitePLBallPair_weighted_corner_rim_caps hm₁ hm₂ ⟨hc.1, hc.2.trans hηtop⟩

end TriangularRoofModel
