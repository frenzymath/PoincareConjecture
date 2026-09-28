import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Parity.CrossingLocal
import Mathlib.Order.Interval.Set.Infinite











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Manifold.Schoenflies.Plane



theorem segmentRayParity_eventually_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X H : E →ₗ[ℝ] ℝ) (hX : Continuous X) (hH : Continuous H)
    (hcoords : Function.Injective (fun x => (X x, H x)))
    {a b q : E} (hab : H a ≠ H b) (hq : q ∉ segment ℝ a b)
    (ha : H a ≠ H q) (hb : H b ≠ H q) :
    ∀ᶠ z in 𝓝 q, segmentRayParity X H a b z = segmentRayParity X H a b q := by
  filter_upwards [segmentRayParity_eventually_eq_factor X H hX hH hcoords hab hq,
    heightStep_eventually_eq hH.continuousAt ha,
    heightStep_eventually_eq hH.continuousAt hb] with z hz hza hzb
  rw [hz, hza, hzb]
  exact (segmentRayParity_factor X H a b q).symm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



theorem segmentRayParity_eq_one_horizontal_left (X H : E →ₗ[ℝ] ℝ)
    {a b q v : E} (hq : q ∈ segment ℝ a b)
    (hband : heightCrossing (H a) (H b) (H q)) (hvX : X v = 1) (hvH : H v = 0)
    {t : ℝ} (ht : 0 < t) : segmentRayParity X H a b (q - t • v) = 1 := by
  have hlevel : H (q - t • v) = H q := by
    simp only [map_sub, map_smul, hvH, smul_zero, sub_zero]
  have hm : lineLevelPoint H a b (H (q - t • v)) = q := by
    rw [hlevel]
    exact lineLevelPoint_eq_of_mem_segment H (heightCrossing_ne hband) hq
  apply if_pos
  refine ⟨by rwa [hlevel], ?_⟩
  rw [hm, map_sub, map_smul, hvX, smul_eq_mul, mul_one]
  linarith



theorem segmentRayParity_eq_zero_horizontal_right (X H : E →ₗ[ℝ] ℝ)
    {a b q v : E} (hab : H a ≠ H b) (hq : q ∈ segment ℝ a b)
    (hvX : X v = 1) (hvH : H v = 0) {t : ℝ} (ht : 0 ≤ t) :
    segmentRayParity X H a b (q + t • v) = 0 := by
  have hlevel : H (q + t • v) = H q := by
    simp only [map_add, map_smul, hvH, smul_zero, add_zero]
  have hm : lineLevelPoint H a b (H (q + t • v)) = q := by
    rw [hlevel]
    exact lineLevelPoint_eq_of_mem_segment H hab hq
  apply segmentRayParity_eq_zero_of_right X H
  rw [hm, map_add, map_smul, hvX, smul_eq_mul, mul_one]
  linarith



theorem exists_mem_segment_height_avoiding_finite (H : E →ₗ[ℝ] ℝ)
    {a b : E} (hab : H a ≠ H b) {s : Set ℝ} (hs : s.Finite) :
    ∃ q ∈ segment ℝ a b, min (H a) (H b) < H q ∧ H q < max (H a) (H b) ∧ H q ∉ s := by
  have hminmax : min (H a) (H b) < max (H a) (H b) := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · simpa only [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa only [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  obtain ⟨y, hy, hys⟩ := (Ioo_infinite hminmax).exists_notMem_finite hs
  refine ⟨lineLevelPoint H a b y,
    (lineLevelPoint_mem_segment_iff H hab y).mpr ⟨hy.1.le, hy.2.le⟩, ?_⟩
  simpa only [linearMap_lineLevelPoint H hab y] using And.intro hy.1 (And.intro hy.2 hys)

end Poincare.Manifold.Schoenflies.Plane
