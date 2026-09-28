import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

open Set Metric
open scoped BigOperators

universe u

namespace Poincare.Topology

open scoped Classical in
theorem abs_weight_le_norm_sum_div_altitude
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Finset E) (v : E) (hv : v ∈ s) (a : Real) (ha : 0 < a)
    (halt : a ≤ infDist v (affineSpan Real ((s.erase v : Finset E) : Set E) : Set E))
    (w : E → Real) (hsum : ∑ x ∈ s, w x = 0) :
    |w v| ≤ ‖∑ x ∈ s, w x • x‖ / a := by
  classical
  by_cases hwv : w v = 0
  · rw [hwv, abs_zero]
    exact div_nonneg (norm_nonneg _) ha.le
  have hrest : ∑ x ∈ s.erase v, w x = -w v := by
    have h := Finset.add_sum_erase s w hv
    rw [hsum] at h
    linarith
  let c (x : E) : Real := -(w v)⁻¹ * w x
  have hcsum : ∑ x ∈ s.erase v, c x = 1 := by
    simp only [c, ← Finset.mul_sum, hrest, neg_mul_neg, inv_mul_cancel₀ hwv]
  let y : E := ∑ x ∈ s.erase v, c x • x
  have hy : y ∈ affineSpan Real ((s.erase v : Finset E) : Set E) := by
    have h := affineCombination_mem_affineSpan_image hcsum
      (s' := (s.erase v : Set E)) (fun x hx hnot => (hnot hx).elim) (fun x : E => x)
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hcsum] at h
    simpa only [Set.image_id'] using h
  have hwy : w v • y = -(∑ x ∈ s.erase v, w x • x) := by
    dsimp [y]
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [smul_smul]
    have hcoef : w v * c x = -w x := by
      dsimp [c]
      field_simp
    rw [hcoef, neg_smul]
  have hu : ∑ x ∈ s, w x • x = w v • (v - y) := by
    rw [smul_sub, hwy, sub_neg_eq_add, Finset.add_sum_erase s (fun x => w x • x) hv]
  have hdist : a ≤ ‖v - y‖ :=
    halt.trans ((infDist_le_dist_of_mem hy).trans_eq (dist_eq_norm _ _))
  apply (le_div_iff₀ ha).mpr
  calc
    |w v| * a ≤ |w v| * ‖v - y‖ := mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
    _ = ‖∑ x ∈ s, w x • x‖ := by rw [hu, norm_smul, Real.norm_eq_abs]

open scoped Classical in
theorem abs_coordinate_sub_le_norm_sum_sub_div_altitude
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (s : Finset E) (v : E) (hv : v ∈ s) (a : Real) (ha : 0 < a)
    (halt : a ≤ infDist v (affineSpan Real ((s.erase v : Finset E) : Set E) : Set E))
    (w w' : E → Real) (hsum : ∑ x ∈ s, w x = ∑ x ∈ s, w' x) :
    |w v - w' v| ≤ ‖(∑ x ∈ s, w x • x) - ∑ x ∈ s, w' x • x‖ / a := by
  have h := abs_weight_le_norm_sum_div_altitude s v hv a ha halt (fun x => w x - w' x)
    (by rw [Finset.sum_sub_distrib, hsum, sub_self])
  simpa only [sub_smul, Finset.sum_sub_distrib] using h

end Poincare.Topology
