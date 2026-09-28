import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Parity.CrossingBasics
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Manifold.Schoenflies.Plane

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def lineSideParity (X H : E →ₗ[ℝ] ℝ) (a b q : E) : ZMod 2 := by
  classical
  exact if X q < X (lineLevelPoint H a b (H q)) then 1 else 0

theorem segmentRayParity_factor (X H : E →ₗ[ℝ] ℝ) (a b q : E) :
    segmentRayParity X H a b q = lineSideParity X H a b q *
      (heightStep (H a) (H q) + heightStep (H b) (H q)) := by
  classical
  by_cases hX : X q < X (lineLevelPoint H a b (H q))
  · rw [segmentRayParity_eq_heightStep_of_left X H hX]
    simp only [lineSideParity, if_pos hX, one_mul]
  · rw [segmentRayParity_eq_zero_of_right X H (le_of_not_gt hX)]
    simp only [lineSideParity, if_neg hX, zero_mul]

end Module

theorem heightStep_eventually_eq {T : Type*} [TopologicalSpace T]
    {f : T → ℝ} {q : T} {a : ℝ} (hf : ContinuousAt f q) (ha : a ≠ f q) :
    ∀ᶠ z in 𝓝 q, heightStep a (f z) = heightStep a (f q) := by
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · filter_upwards [hf.eventually (eventually_gt_nhds hlt)] with z hz
    simp only [heightStep, if_pos hlt.le, if_pos hz.le]
  · filter_upwards [hf.eventually (eventually_lt_nhds hgt)] with z hz
    simp only [heightStep, if_neg (not_le_of_gt hgt), if_neg (not_le_of_gt hz)]

theorem segmentRayParity_eventually_eq_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X H : E →ₗ[ℝ] ℝ) (hX : Continuous X) (hH : Continuous H)
    (hcoords : Function.Injective (fun x => (X x, H x)))
    {a b q : E} (hab : H a ≠ H b) (hq : q ∉ segment ℝ a b) :
    ∀ᶠ z in 𝓝 q, segmentRayParity X H a b z = lineSideParity X H a b q *
      (heightStep (H a) (H z) + heightStep (H b) (H z)) := by
  classical
  by_cases hlo : min (H a) (H b) ≤ H q
  · by_cases hhi : H q ≤ max (H a) (H b)
    · have hm := (lineLevelPoint_mem_segment_iff H hab (H q)).mpr ⟨hlo, hhi⟩
      have hne : X q ≠ X (lineLevelPoint H a b (H q)) := by
        intro heq
        have he : q = lineLevelPoint H a b (H q) :=
          hcoords (Prod.ext heq (linearMap_lineLevelPoint H hab (H q)).symm)
        exact hq (he.symm ▸ hm)
      have hmcont : Continuous (fun z => X (lineLevelPoint H a b (H z))) :=
        hX.comp ((contDiff_lineLevelPoint H a b).continuous.comp hH)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · filter_upwards [hX.continuousAt.eventually_lt hmcont.continuousAt hlt] with z hz
        rw [segmentRayParity_eq_heightStep_of_left X H hz]
        simp only [lineSideParity, if_pos hlt, one_mul]
      · filter_upwards [hmcont.continuousAt.eventually_lt hX.continuousAt hgt] with z hz
        rw [segmentRayParity_eq_zero_of_right X H hz.le]
        simp only [lineSideParity, if_neg (not_lt_of_ge hgt.le), zero_mul]
    · filter_upwards [hH.continuousAt.eventually
        (eventually_gt_nhds (lt_of_not_ge hhi))] with z hz
      have hnc : ¬heightCrossing (H a) (H b) (H z) :=
        fun hc => not_lt_of_ge hz.le hc.2
      rw [← heightCrossing_indicator]
      simp only [segmentRayParity, segmentCrossesRay, hnc, false_and, if_false, mul_zero]
  · filter_upwards [hH.continuousAt.eventually
      (eventually_lt_nhds (lt_of_not_ge hlo))] with z hz
    have hnc : ¬heightCrossing (H a) (H b) (H z) :=
      fun hc => not_le_of_gt hz hc.1
    rw [← heightCrossing_indicator]
    simp only [segmentRayParity, segmentCrossesRay, hnc, false_and, if_false, mul_zero]

end Poincare.Manifold.Schoenflies.Plane
