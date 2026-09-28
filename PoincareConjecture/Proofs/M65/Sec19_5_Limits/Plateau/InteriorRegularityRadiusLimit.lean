import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M65Interior

private theorem radius_sub_le_power {f : ℝ → ℝ} {C β s r : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hsr : s ≤ r)
    (hf : ∀ t ∈ Icc s r, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Icc s r, deriv f t ≤ C * t ^ (β - 1)) :
    f r - f s ≤ (C / β) * (r ^ β - s ^ β) := by
  let g : ℝ → ℝ := fun t => (C / β) * t ^ β - f t
  have hd (t : ℝ) (ht : t ∈ Icc s r) :
      HasDerivAt g (C * t ^ (β - 1) - deriv f t) t := by
    have ht0 : 0 < t := hs.trans_le ht.1
    have hd := ((Real.hasDerivAt_rpow_const (p := β) (Or.inl ht0.ne')).const_mul
      (C / β)).sub (hf t ht).hasDerivAt
    change HasDerivAt g _ t at hd
    apply hd.congr_deriv
    field_simp
  have hm : MonotoneOn g (Icc s r) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s r)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hb t (interior_subset ht))
  have h := hm (left_mem_Icc.mpr hsr) (right_mem_Icc.mpr hsr) hsr
  dsimp only [g] at h
  linarith only [h]

theorem radius_increment_le_power {f : ℝ → ℝ} {C β s r : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hsr : s ≤ r)
    (hf : ∀ t ∈ Icc s r, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Icc s r, |deriv f t| ≤ C * t ^ (β - 1)) :
    |f r - f s| ≤ (C / β) * (r ^ β - s ^ β) := by
  have hp := radius_sub_le_power hβ hs hsr hf
    (fun t ht => (le_abs_self _).trans (hb t ht))
  have hn := radius_sub_le_power (f := fun t => -f t) (C := C) hβ hs hsr
    (fun t ht => (hf t ht).neg) (fun t ht => by
      change deriv (-f) t ≤ C * t ^ (β - 1)
      rw [(hf t ht).hasDerivAt.neg.deriv]
      exact (neg_le_abs _).trans (hb t ht))
  rw [abs_le]
  constructor <;> linarith only [hp, hn]

theorem exists_radius_limit {f : ℝ → ℝ} {C β R : ℝ}
    (hC : 0 ≤ C) (hβ : 0 < β) (hR : 0 < R)
    (hf : ∀ r ∈ Ioc 0 R, DifferentiableAt ℝ f r)
    (hb : ∀ r ∈ Ioc 0 R, |deriv f r| ≤ C * r ^ (β - 1)) :
    ∃ a : ℝ, Tendsto f (𝓝[>] 0) (𝓝 a) ∧
      ∀ r ∈ Ioc 0 R, |f r - a| ≤ (C / β) * r ^ β := by
  let K := C / β
  have hK : 0 ≤ K := div_nonneg hC hβ.le
  have hincr {s r : ℝ} (hs : s ∈ Ioc 0 R) (hr : r ∈ Ioc 0 R) (hsr : s ≤ r) :
      |f r - f s| ≤ K * (r ^ β - s ^ β) :=
    radius_increment_le_power hβ hs.1 hsr
      (fun t ht => hf t ⟨hs.1.trans_le ht.1, ht.2.trans hr.2⟩)
      (fun t ht => hb t ⟨hs.1.trans_le ht.1, ht.2.trans hr.2⟩)
  have hpair {s r : ℝ} (hs : s ∈ Ioc 0 R) (hr : r ∈ Ioc 0 R) :
      dist (f r) (f s) ≤ K * r ^ β + K * s ^ β := by
    rw [Real.dist_eq]
    rcases le_total s r with hsr | hrs
    · have h := hincr hs hr hsr
      nlinarith only [h, mul_nonneg hK (Real.rpow_nonneg hs.1.le β)]
    · rw [abs_sub_comm]
      have h := hincr hr hs hrs
      nlinarith only [h, mul_nonneg hK (Real.rpow_nonneg hr.1.le β)]
  have hp : Tendsto (fun r : ℝ => K * r ^ β) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne', mul_zero] using
      (tendsto_const_nhds.mul
        ((Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.mono_left
          nhdsWithin_le_nhds) :
        Tendsto (fun r : ℝ => K * r ^ β) (𝓝[>] 0) (𝓝 (K * 0 ^ β)))
  have hc : Cauchy (map f (𝓝[>] 0)) := by
    refine Metric.cauchy_iff.mpr ⟨inferInstance, ?_⟩
    intro ε hε
    let A := {r : ℝ | r ∈ Ioc 0 R ∧ K * r ^ β < ε / 2}
    have hA : A ∈ 𝓝[>] (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhdsGT hR, hp.eventually (gt_mem_nhds (half_pos hε))] with r hr hb'
      exact ⟨⟨hr.1, hr.2.le⟩, hb'⟩
    refine ⟨f '' A, image_mem_map hA, ?_⟩
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    exact (hpair hs.1 hr.1).trans_lt (by linarith only [hr.2, hs.2])
  obtain ⟨a, ha⟩ := cauchy_map_iff_exists_tendsto.mp hc
  refine ⟨a, ha, ?_⟩
  intro r hr
  apply le_of_tendsto (tendsto_const_nhds.sub ha).abs
  filter_upwards [Ioo_mem_nhdsGT hr.1] with s hs
  have h := hincr ⟨hs.1, hs.2.le.trans hr.2⟩ hr hs.2.le
  have hn := mul_nonneg hK (Real.rpow_nonneg hs.1.le β)
  change |f r - f s| ≤ K * r ^ β
  nlinarith only [h, hn]

end PoincareConjecture.M65Interior
