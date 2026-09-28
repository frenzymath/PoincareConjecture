import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCrossingJump
import Mathlib.Topology.Order.LeftRight









set_option autoImplicit false

open Set Filter PlanarSegment
open scoped Topology

namespace Polygon




theorem exists_crossingIndex_unit_jump {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (hnv : P.HasNonverticalEdges) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      P.crossingIndex a - P.crossingIndex b = 1 ∨
      P.crossingIndex a - P.crossingIndex b = -1 := by
  obtain ⟨q, hqi, hreg, hother⟩ := P.exists_regular_point_on_edge hP hinj hnv 0
  have hqv : q ∉ range P := by
    rintro ⟨j, rfl⟩
    exact hreg j rfl
  have hsegment := (mem_segment_iff (hnv 0)).mp (show
      q ∈ segment ℝ (P 0) (P (finRotate (n + 3) 0)) by
    simpa only [edgeSet, affineSegment_eq_segment] using hqi)
  let d := horizontalStep (P 0).1 q - horizontalStep (P (finRotate (n + 3) 0)).1 q
  have hd : d = 1 ∨ d = -1 := by
    rcases mem_uIcc.mp hsegment.1 with h | h
    · have hb := lt_of_le_of_ne h.2 (hreg _)
      left
      norm_num only [d, horizontalStep, if_pos h.1, if_neg (not_le_of_gt hb)]
    · have ha := lt_of_le_of_ne h.2 (hreg _)
      right
      norm_num only [d, horizontalStep, if_pos h.1, if_neg (not_le_of_gt ha)]
  have hlocal : ∀ᶠ y in 𝓝 q.2, (q.1, y) ∈ P.boundary ℝ ↔ y = q.2 := by
    have hc : Continuous (fun y : ℝ => (q.1, y)) := continuous_const.prodMk continuous_id
    filter_upwards [(hc.tendsto q.2).eventually
      (P.eventually_boundary_iff_single_edge hP hinj hqv hqi)] with y hy
    rw [hy, edgeSet, affineSegment_eq_segment, mem_segment_iff (hnv 0)]
    simpa only [hsegment.1, true_and] using
      (show y = height (P 0) (P (finRotate (n + 3) 0)) q.1 ↔ y = q.2 by rw [hsegment.2])
  have hnear := (P.eventually_crossingIndex_vertical hnv hqi hother).and hlocal
  obtain ⟨l, hl, hli, hlb⟩ := ((frequently_lt_nhds q.2).and_eventually hnear).exists
  obtain ⟨u, hu, hui, hub⟩ := ((frequently_gt_nhds q.2).and_eventually hnear).exists
  refine ⟨(q.1, l), fun h => hl.ne (hlb.mp h),
    (q.1, u), fun h => hu.ne' (hub.mp h), ?_⟩
  simp only [if_pos hl, mul_one] at hli
  simp only [if_neg (not_lt_of_ge hu.le), mul_zero, add_zero] at hui
  rw [hli, hui]
  change P.crossingIndex q + d - P.crossingIndex q = 1 ∨
    P.crossingIndex q + d - P.crossingIndex q = -1
  omega

end Polygon
