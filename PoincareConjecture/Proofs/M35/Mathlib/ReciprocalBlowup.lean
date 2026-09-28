import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Set
open scoped Topology

theorem inv_mul_time_sub_le_of_tendsto_atTop
    {f f' : ℝ → ℝ} {a b A : ℝ} (hA : 0 < A)
    (hpos : ∀ t ∈ Ico a b, 0 < f t)
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ico a b) t)
    (hbound : ∀ t ∈ Ico a b, f' t ≤ A * (f t) ^ 2)
    (hblow : Tendsto f (𝓝[<] b) atTop) :
    ∀ t ∈ Ico a b, (A * (b - t))⁻¹ ≤ f t := by
  have hq (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt (fun s => (f s)⁻¹ + A * s)
        (-f' t / (f t) ^ 2 + A) (Ico a b) t := by
    convert! ((hderiv t ht).inv (hpos t ht).ne').add
      ((hasDerivWithinAt_id t (Ico a b)).const_mul A) using 1
    simp only [mul_one]
  have hmono : MonotoneOn (fun s => (f s)⁻¹ + A * s) (Ico a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico a b)
      (fun t ht => (hq t ht).continuousWithinAt)
      (fun t ht => (hq t (interior_subset ht)).mono interior_subset)
    intro t ht
    have ht' := interior_subset ht
    have hsq : 0 < (f t) ^ 2 := sq_pos_of_pos (hpos t ht')
    have hdiv : f' t / (f t) ^ 2 ≤ A := (div_le_iff₀ hsq).2 (hbound t ht')
    rw [neg_div]
    linarith
  have hlimit : Tendsto (fun s => (f s)⁻¹ + A * s) (𝓝[<] b) (𝓝 (A * b)) := by
    simpa only [Pi.inv_apply, id_eq, zero_add] using
      hblow.inv_tendsto_atTop.add
        (tendsto_const_nhds.mul (tendsto_id'.2 nhdsWithin_le_nhds))
  intro t ht
  have hle : (f t)⁻¹ + A * t ≤ A * b := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds ht.2).filter_mono nhdsWithin_le_nhds] with s hs hst
    exact hmono ht ⟨ht.1.trans hst.le, hs⟩ hst.le
  have hrecip : (f t)⁻¹ ≤ A * (b - t) := by linarith
  exact (inv_le_comm₀ (mul_pos hA (sub_pos.mpr ht.2)) (hpos t ht)).2 hrecip
