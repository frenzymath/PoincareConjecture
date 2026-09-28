import PoincareConjecture.Proofs.M76.Mathlib.PlanarSegmentCap
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PlanarSegment

theorem exists_cap_point_towards_lower {q a : ℝ × ℝ}
    (hqx : 0 < q.1) (hqy : 0 < q.2) (hqh : q.1 + q.2 = 1)
    (hah : a.1 + a.2 < 1) :
    ∃ r ∈ openSegment ℝ q a, 0 < r.1 ∧ 0 < r.2 ∧ r.1 + r.2 < 1 := by
  let f : ℝ → ℝ × ℝ := AffineMap.lineMap q a
  have hf : Continuous f := by
    change Continuous (fun t : ℝ => AffineMap.lineMap q a t)
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (f t).1 ∧ 0 < (f t).2 :=
    ((isOpen_lt continuous_const (continuous_fst.comp hf)).inter
      (isOpen_lt continuous_const (continuous_snd.comp hf))).mem_nhds
        (by
          change 0 < (f 0).1 ∧ 0 < (f 0).2
          simpa only [f, AffineMap.lineMap_apply_zero] using And.intro hqx hqy)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpos
  let t := min ε 1 / 2
  have ht : 0 < t := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have htε : t < ε := by dsimp [t]; linarith [min_le_left ε 1]
  have ht1 : t < 1 := by dsimp [t]; linarith [min_le_right ε 1]
  have hp := hball (show t ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htε)
  refine ⟨f t, lineMap_mem_openSegment ℝ q a ⟨ht, ht1⟩, hp.1, hp.2, ?_⟩
  dsimp [f]
  rw [AffineMap.lineMap_apply_module']
  change t * (a.1 - q.1) + q.1 + (t * (a.2 - q.2) + q.2) < 1
  nlinarith [mul_neg_of_pos_of_neg ht (sub_neg.mpr hah)]

theorem endpoint_heights_eq_of_miss_cap {a b q : ℝ × ℝ}
    (hq : q ∈ openSegment ℝ a b) (hqx : 0 < q.1) (hqy : 0 < q.2)
    (hqh : q.1 + q.2 = 1)
    (hmiss : ∀ r ∈ segment ℝ a b, ¬ (0 < r.1 ∧ 0 < r.2 ∧ r.1 + r.2 < 1)) :
    a.1 + a.2 = 1 ∧ b.1 + b.2 = 1 := by
  have hqseg := openSegment_subset_segment ℝ a b hq
  have hnotlow (r : ℝ × ℝ) (hr : r ∈ segment ℝ a b) : 1 ≤ r.1 + r.2 := by
    by_contra h
    obtain ⟨s, hs, hscap⟩ := exists_cap_point_towards_lower hqx hqy hqh (lt_of_not_ge h)
    exact hmiss s ((convex_segment (𝕜 := ℝ) a b).segment_subset hqseg hr
      (openSegment_subset_segment ℝ q r hs)) hscap
  have ha := hnotlow a (left_mem_segment ℝ a b)
  have hb := hnotlow b (right_mem_segment ℝ a b)
  obtain ⟨s, t, hs, ht, hst, hqeq⟩ := hq
  have hx := congrArg Prod.fst hqeq
  have hy := congrArg Prod.snd hqeq
  change s * a.1 + t * b.1 = q.1 at hx
  change s * a.2 + t * b.2 = q.2 at hy
  constructor
  · apply le_antisymm _ ha
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hb)]
  · apply le_antisymm _ hb
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr ha)]

end PlanarSegment
