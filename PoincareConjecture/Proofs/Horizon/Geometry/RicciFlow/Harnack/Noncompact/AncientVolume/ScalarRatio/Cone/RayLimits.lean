import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.OppositeSegments
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

open Splitting (segmentComparisonCosine)

private theorem comparison_cosine_bounds {X : Type*} [MetricSpace X]
    (minus plus : ℝ → X) (hzero : minus 0 = plus 0)
    (hminus : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (minus s) (minus t) = |s - t|)
    (hplus : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (plus s) (plus t) = |s - t|)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    -1 ≤ segmentComparisonCosine minus plus a b ∧
      segmentComparisonCosine minus plus a b ≤ 1 := by
  have hm : dist (minus a) (minus 0) = a := by
    rw [hminus a ha.le 0 le_rfl, sub_zero, abs_of_nonneg ha.le]
  have hp : dist (plus b) (minus 0) = b := by
    rw [hzero, hplus b hb.le 0 le_rfl, sub_zero, abs_of_nonneg hb.le]
  have hupper : dist (minus a) (plus b) ≤ a + b := by
    simpa only [hm, dist_comm (minus 0) (plus b), hp] using
      dist_triangle (minus a) (minus 0) (plus b)
  have hleft : a ≤ dist (minus a) (plus b) + b := by
    simpa only [hm, hp] using dist_triangle (minus a) (plus b) (minus 0)
  have hright : b ≤ dist (minus a) (plus b) + a := by
    simpa only [hm, hp, dist_comm (plus b) (minus a)] using
      dist_triangle (plus b) (minus a) (minus 0)
  have hlower : |a - b| ≤ dist (minus a) (plus b) := by
    rw [abs_le]
    constructor <;> linarith
  have hsqupper := pow_le_pow_left₀ dist_nonneg hupper 2
  have hsqlower := pow_le_pow_left₀ (abs_nonneg (a - b)) hlower 2
  rw [sq_abs] at hsqlower
  have hden : 0 < 2 * a * b := by positivity
  constructor
  · rw [segmentComparisonCosine, le_div_iff₀ hden]
    nlinarith
  · rw [segmentComparisonCosine, div_le_iff₀ hden]
    nlinarith

private theorem comparison_cosine_mono {X : Type*} [MetricSpace X]
    (minus plus : ℝ → X)
    (hcomparison : ∀ a b : ℝ, 0 < a → 0 < b →
      ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
        s ^ 2 + t ^ 2 - 2 * s * t * segmentComparisonCosine minus plus a b ≤
          dist (minus s) (plus t) ^ 2)
    {a b s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hsa : s ≤ a) (htb : t ≤ b) :
    segmentComparisonCosine minus plus s t ≤ segmentComparisonCosine minus plus a b := by
  have h := hcomparison a b (hs.trans_le hsa) (ht.trans_le htb)
    s ⟨hs.le, hsa⟩ t ⟨ht.le, htb⟩
  rw [segmentComparisonCosine, div_le_iff₀ (by positivity : 0 < 2 * s * t)]
  nlinarith

theorem exists_homogeneous_ray_distance_limit {X : Type*} [MetricSpace X]
    (minus plus : ℝ → X) (hzero : minus 0 = plus 0)
    (hminus : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (minus s) (minus t) = |s - t|)
    (hplus : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (plus s) (plus t) = |s - t|)
    (hcomparison : ∀ a b : ℝ, 0 < a → 0 < b →
      ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
        s ^ 2 + t ^ 2 - 2 * s * t * segmentComparisonCosine minus plus a b ≤
          dist (minus s) (plus t) ^ 2) :
    ∃ q ∈ Icc (-1 : ℝ) 1, ∀ r s : ℝ, 0 < r → 0 < s →
      Tendsto (fun L : ℝ => segmentComparisonCosine minus plus (r * L) (s * L))
        atTop (𝓝 q) ∧
      Tendsto (fun L : ℝ => dist (minus (r * L)) (plus (s * L)) / L)
        atTop (𝓝 (Real.sqrt (r ^ 2 + s ^ 2 - 2 * r * s * q))) := by
  let f : ℝ → ℝ := fun L => segmentComparisonCosine minus plus (max L 1) (max L 1)
  have hfmono : Monotone f := by
    intro a b hab
    exact comparison_cosine_mono minus plus hcomparison
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (max_le_max_right _ hab) (max_le_max_right _ hab)
  have hfbounds (L : ℝ) : -1 ≤ f L ∧ f L ≤ 1 :=
    comparison_cosine_bounds minus plus hzero hminus hplus
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hfbdd : BddAbove (range f) := ⟨1, by rintro _ ⟨L, rfl⟩; exact (hfbounds L).2⟩
  let q := ⨆ L, f L
  have hf : Tendsto f atTop (𝓝 q) := tendsto_atTop_ciSup hfmono hfbdd
  have hq : q ∈ Icc (-1 : ℝ) 1 := by
    exact ⟨le_trans (hfbounds 0).1 (le_ciSup hfbdd 0), ciSup_le (fun L => (hfbounds L).2)⟩
  refine ⟨q, hq, ?_⟩
  intro r s hr hs
  have hmin : 0 < min r s := lt_min hr hs
  have hmax : 0 < max r s := hr.trans_le (le_max_left _ _)
  have hminlim : Tendsto (fun L : ℝ => min r s * L) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hmin).2 tendsto_id
  have hmaxlim : Tendsto (fun L : ℝ => max r s * L) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hmax).2 tendsto_id
  have hcos : Tendsto (fun L : ℝ =>
      segmentComparisonCosine minus plus (r * L) (s * L)) atTop (𝓝 q) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hf.comp hminlim) (hf.comp hmaxlim)
    · filter_upwards [hminlim.eventually_ge_atTop 1, eventually_ge_atTop (0 : ℝ)] with L hL hL0
      change segmentComparisonCosine minus plus (max (min r s * L) 1)
        (max (min r s * L) 1) ≤ _
      rw [max_eq_left hL]
      exact comparison_cosine_mono minus plus hcomparison (zero_lt_one.trans_le hL)
        (zero_lt_one.trans_le hL) (mul_le_mul_of_nonneg_right (min_le_left _ _) hL0)
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hL0)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      exact comparison_cosine_mono minus plus hcomparison (mul_pos hr hL) (mul_pos hs hL)
        ((mul_le_mul_of_nonneg_right (le_max_left _ _) hL.le).trans (le_max_left _ _))
        ((mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le).trans (le_max_left _ _))
  refine ⟨hcos, ?_⟩
  have hsq : Tendsto (fun L : ℝ =>
      (dist (minus (r * L)) (plus (s * L)) / L) ^ 2)
      atTop (𝓝 (r ^ 2 + s ^ 2 - 2 * r * s * q)) := by
    have h := (tendsto_const_nhds (x := r ^ 2 + s ^ 2)).sub
      ((tendsto_const_nhds (x := 2 * r * s)).mul hcos)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [segmentComparisonCosine]
    field_simp
    ring
  apply hsq.sqrt.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact Real.sqrt_sq (div_nonneg dist_nonneg hL.le)

end Poincare.AncientVolume.ScalarRatio
