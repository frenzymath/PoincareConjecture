import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set

namespace PlanarSegment

private theorem sum_mem_uIcc {a b q : ℝ × ℝ} (hq : q ∈ segment ℝ a b) :
    q.1 + q.2 ∈ uIcc (a.1 + a.2) (b.1 + b.2) := by
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ
  have h := mem_image_of_mem L.toAffineMap hq
  rw [image_segment, segment_eq_uIcc] at h
  exact h

private theorem positive_of_low_endpoint {a b q : ℝ × ℝ} {h : ℝ}
    (hq : q ∈ segment ℝ a b) (hqx : 0 < q.1) (hqy : 0 < q.2)
    (hqh : q.1 + q.2 < h) (hah : a.1 + a.2 < h)
    (havoid : ∀ r ∈ segment ℝ a b,
      ¬ ((r.1 = 0 ∧ 0 ≤ r.2 ∧ r.2 < h) ∨ (r.2 = 0 ∧ 0 ≤ r.1 ∧ r.1 < h))) :
    0 < a.1 ∧ 0 < a.2 := by
  by_contra hpos
  have hmin : min a.1 a.2 ≤ 0 := by
    simpa only [not_and_or, not_lt, min_le_iff] using hpos
  have hcont : Continuous (fun r : ℝ × ℝ => min r.1 r.2) := continuous_fst.min continuous_snd
  obtain ⟨r, hr, hzero⟩ := (convex_segment (𝕜 := ℝ) a q).isPreconnected.intermediate_value
    (left_mem_segment ℝ a q) (right_mem_segment ℝ a q) hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (min a.1 a.2) (min q.1 q.2) from
      ⟨hmin, le_min hqx.le hqy.le⟩)
  change min r.1 r.2 = 0 at hzero
  have hrab : r ∈ segment ℝ a b :=
    (convex_segment (𝕜 := ℝ) a b).segment_subset (left_mem_segment ℝ a b) hq hr
  have hrh : r.1 + r.2 < h :=
    lt_of_le_of_lt (sum_mem_uIcc hr).2 (max_lt hah hqh)
  have hrnonneg : 0 ≤ r.1 ∧ 0 ≤ r.2 := le_min_iff.mp hzero.ge
  have haxis : r.1 = 0 ∨ r.2 = 0 := by
    rcases le_total r.1 r.2 with hle | hle
    · exact Or.inl (by rwa [min_eq_left hle] at hzero)
    · exact Or.inr (by rwa [min_eq_right hle] at hzero)
  apply havoid r hrab
  rcases haxis with hx | hy
  · exact Or.inl ⟨hx, hrnonneg.2, by simpa only [hx, zero_add] using hrh⟩
  · exact Or.inr ⟨hy, hrnonneg.1, by simpa only [hy, add_zero] using hrh⟩




theorem endpoint_mem_cap_of_inter {a b q : ℝ × ℝ} {h : ℝ}
    (hq : q ∈ segment ℝ a b) (hqx : 0 < q.1) (hqy : 0 < q.2)
    (hqh : q.1 + q.2 < h)
    (havoid : ∀ r ∈ segment ℝ a b,
      ¬ ((r.1 = 0 ∧ 0 ≤ r.2 ∧ r.2 < h) ∨ (r.2 = 0 ∧ 0 ≤ r.1 ∧ r.1 < h))) :
    (0 < a.1 ∧ 0 < a.2 ∧ a.1 + a.2 < h) ∨
      (0 < b.1 ∧ 0 < b.2 ∧ b.1 + b.2 < h) := by
  have hlow := min_le_iff.mp (sum_mem_uIcc hq).1
  rcases hlow with ha | hb
  · have hh := ha.trans_lt hqh
    have hp := positive_of_low_endpoint hq hqx hqy hqh hh havoid
    exact Or.inl ⟨hp.1, hp.2, hh⟩
  · have hh := hb.trans_lt hqh
    have hp := positive_of_low_endpoint (by rwa [segment_symm]) hqx hqy hqh hh
      (fun r hr => havoid r (by rwa [segment_symm] at hr))
    exact Or.inr ⟨hp.1, hp.2, hh⟩

end PlanarSegment
