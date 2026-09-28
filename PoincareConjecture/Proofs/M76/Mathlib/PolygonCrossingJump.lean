import PoincareConjecture.Proofs.M76.Mathlib.PolygonCrossingIndex
import Mathlib.Topology.MetricSpace.Pseudo.Defs










set_option autoImplicit false

open Set Filter PlanarSegment
open scoped Topology BigOperators

namespace Polygon

variable {n : ℕ}

private theorem eventually_vertical_avoids {a b q : ℝ × ℝ}
    (hab : a.1 ≠ b.1) (hq : q ∉ segment ℝ a b) :
    ∀ᶠ y in 𝓝 q.2, (q.1, y) ∉ segment ℝ a b := by
  by_cases hx : q.1 ∈ uIcc a.1 b.1
  · have hy : q.2 ≠ height a b q.1 := fun h => hq ((mem_segment_iff hab).mpr ⟨hx, h⟩)
    filter_upwards [eventually_ne_nhds hy] with y hy
    simpa only [mem_segment_iff hab, hx, true_and] using hy
  · exact Eventually.of_forall fun y => by simp only [mem_segment_iff hab, hx, false_and,
      not_false_eq_true]

private theorem eventually_vertical_contribution {a b q : ℝ × ℝ}
    (hab : a.1 ≠ b.1) (hq : q ∉ segment ℝ a b) :
    ∀ᶠ y in 𝓝 q.2, crossingContribution a b (q.1, y) = crossingContribution a b q := by
  have hc : Continuous (fun y : ℝ => (q.1, y)) := continuous_const.prodMk continuous_id
  filter_upwards [hc.continuousAt.eventually (eventually_crossingContribution hab hq)]
    with y hy
  simpa only [crossingContribution, horizontalStep] using hy





theorem eventually_crossingIndex_vertical (P : Polygon (ℝ × ℝ) n)
    (hP : P.HasNonverticalEdges) {q : ℝ × ℝ} {i : Fin n}
    (hqi : q ∈ P.edgeSet ℝ i)
    (hother : ∀ j, j ≠ i → q ∉ P.edgeSet ℝ j) :
    ∀ᶠ y in 𝓝 q.2,
      P.crossingIndex (q.1, y) = P.crossingIndex q +
        (horizontalStep (P i).1 q - horizontalStep (P (finRotate n i)).1 q) *
          (if y < q.2 then 1 else 0) := by
  classical
  have hheight : q.2 = height (P i) (P (finRotate n i)) q.1 :=
    ((mem_segment_iff (hP i)).mp (by
      simpa only [edgeSet, affineSegment_eq_segment] using hqi)).2
  have hzero : crossingContribution (P i) (P (finRotate n i)) q = 0 := by
    simp only [crossingContribution, aboveLine, ← hheight, lt_self_iff_false,
      if_false, mul_zero]
  have hrest (j : Fin n) (hj : j ∈ Finset.univ.erase i) : ∀ᶠ y in 𝓝 q.2,
      crossingContribution (P j) (P (finRotate n j)) (q.1, y) =
        crossingContribution (P j) (P (finRotate n j)) q := by
    apply eventually_vertical_contribution (hP j)
    simpa only [edgeSet, affineSegment_eq_segment] using
      hother j (Finset.ne_of_mem_erase hj)
  filter_upwards [(Finset.univ.erase i).eventually_all.mpr hrest] with y hy
  have hsum : (∑ j ∈ Finset.univ.erase i,
      crossingContribution (P j) (P (finRotate n j)) (q.1, y)) =
      ∑ j ∈ Finset.univ.erase i, crossingContribution (P j) (P (finRotate n j)) q :=
    Finset.sum_congr rfl fun j hj => hy j hj
  unfold crossingIndex
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ (fun j => crossingContribution (P j) (P (finRotate n j)) q)
      (Finset.mem_univ i), hsum, hzero, add_zero]
  simp only [crossingContribution, aboveLine, ← hheight, horizontalStep]




theorem exists_crossingIndex_ne_of_isolated_edge (P : Polygon (ℝ × ℝ) n)
    (hP : P.HasNonverticalEdges) {q : ℝ × ℝ} {i : Fin n}
    (hqi : q ∈ P.edgeSet ℝ i) (hregular : ∀ j, q.1 ≠ (P j).1)
    (hother : ∀ j, j ≠ i → q ∉ P.edgeSet ℝ j) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      P.crossingIndex a ≠ P.crossingIndex b := by
  classical
  have hsegment := (mem_segment_iff (hP i)).mp (show
      q ∈ segment ℝ (P i) (P (finRotate n i)) by
    simpa only [edgeSet, affineSegment_eq_segment] using hqi)
  let d := horizontalStep (P i).1 q - horizontalStep (P (finRotate n i)).1 q
  have hd : d ≠ 0 := by
    rcases mem_uIcc.mp hsegment.1 with h | h
    · have hb : q.1 < (P (finRotate n i)).1 := lt_of_le_of_ne h.2 (hregular _)
      norm_num only [d, horizontalStep, if_pos h.1, if_neg (not_le_of_gt hb)]
    · have ha : q.1 < (P i).1 := lt_of_le_of_ne h.2 (hregular _)
      norm_num only [d, horizontalStep, if_pos h.1, if_neg (not_le_of_gt ha)]
  have havoid (j : Fin n) : ∀ᶠ y in 𝓝 q.2, j ≠ i → (q.1, y) ∉ P.edgeSet ℝ j := by
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ => fun h => (h hji).elim
    · have hj := eventually_vertical_avoids (hP j) (show
          q ∉ segment ℝ (P j) (P (finRotate n j)) by
        simpa only [edgeSet, affineSegment_eq_segment] using hother j hji)
      filter_upwards [hj] with y hy
      simpa only [edgeSet, affineSegment_eq_segment] using fun _ : j ≠ i => hy
  have hnear := (P.eventually_crossingIndex_vertical hP hqi hother).and
    (Filter.eventually_all.mpr havoid)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hlow : q.2 - ε / 2 ∈ Metric.ball q.2 ε := by
    rw [Metric.mem_ball, Real.dist_eq,
      show q.2 - ε / 2 - q.2 = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hhigh : q.2 + ε / 2 ∈ Metric.ball q.2 ε := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hlowlt : q.2 - ε / 2 < q.2 := sub_lt_self _ (half_pos hε)
  have hhighgt : q.2 < q.2 + ε / 2 := lt_add_of_pos_right _ (half_pos hε)
  have hcomp (y : ℝ) (hy : y ≠ q.2)
      (havoids : ∀ j, j ≠ i → (q.1, y) ∉ P.edgeSet ℝ j) :
      (q.1, y) ∈ (P.boundary ℝ)ᶜ := by
    intro hm
    obtain ⟨j, hj⟩ := mem_iUnion.mp hm
    by_cases hji : j = i
    · subst j
      have hj' := (mem_segment_iff (hP i)).mp (show
          (q.1, y) ∈ segment ℝ (P i) (P (finRotate n i)) by
        simpa only [edgeSet, affineSegment_eq_segment] using hj)
      exact hy (hj'.2.trans hsegment.2.symm)
    · exact havoids j hji hj
  refine ⟨_, hcomp _ hlowlt.ne (hball hlow).2,
    _, hcomp _ hhighgt.ne' (hball hhigh).2, ?_⟩
  have hl := (hball hlow).1
  have hh := (hball hhigh).1
  simp only [if_pos hlowlt, mul_one] at hl
  simp only [if_neg (not_lt_of_ge hhighgt.le), mul_zero, add_zero] at hh
  rw [hl, hh]
  change P.crossingIndex q + d ≠ P.crossingIndex q
  omega

end Polygon
