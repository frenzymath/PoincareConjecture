import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricGradient
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem metricEntropyGradientLp_difference_integral (g h : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (Q : ℝ)
    (u : Lp V 2 (volume : Measure V)) :
    (∫ x, ‖metricEntropyGradient g η Q (x, u x) -
      metricEntropyGradient h η Q (x, u x)‖ ^ 2) =
      ‖metricEntropyGradientLp g hη hc Q u - metricEntropyGradientLp h hη hc Q u‖ ^ 2 := by
  rw [← integral_field_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (metricEntropyGradientLp g hη hc Q u)
      (metricEntropyGradientLp h hη hc Q u),
    metricEntropyGradientLp_coe g hη hc Q u, metricEntropyGradientLp_coe h hη hc Q u]
    with x hx hg hh
  simp only [hx, Pi.sub_apply, hg, hh]

theorem metricEntropyGradientLp_time_continuousOn {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (Q : ℝ) (u : Lp V 2 (volume : Measure V)) :
    ContinuousOn (fun t => metricEntropyGradientLp (F.metric t) hη hc Q u) I := by
  obtain ⟨C, hC, hb⟩ := metricEntropyGradient_slab_bound F hI hIJ hη.continuous hc Q
  intro t ht
  let G (s : ℝ) (x : V) := metricEntropyGradient (F.metric s) η Q (x, u x)
  have hm (s : ℝ) : AEStronglyMeasurable (G s) volume :=
    (metricEntropyGradient_memLp (F.metric s) hη hc Q u).1
  have hb' (s : ℝ) (hs : s ∈ I) (x : V) :
      ‖‖G s x - G t x‖ ^ 2‖ ≤ (2 * C) ^ 2 * ‖u x‖ ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hd : ‖G s x - G t x‖ ≤ (2 * C) * ‖u x‖ := by
      exact ((norm_sub_le _ _).trans (add_le_add (hb s hs x (u x))
        (hb t ht x (u x)))).trans (by ring_nf; rfl)
    calc
      _ ≤ ((2 * C) * ‖u x‖) ^ 2 := by gcongr
      _ = _ := mul_pow _ _ _
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[I] t) (F := fun s x => ‖G s x - G t x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => (2 * C) ^ 2 * ‖u x‖ ^ 2)
    (Eventually.of_forall fun s => ((hm s).sub (hm t)).norm.pow 2)
    (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact Eventually.of_forall fun x => hb' s hs x)
    (((Lp.memLp u).norm.integrable_sq).const_mul ((2 * C) ^ 2))
    (by
      apply Eventually.of_forall
      intro x
      have hpoint := ((metricEntropyGradient_time_continuousOn F η Q x (u x)).mono hIJ) t ht
      simpa only [G, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (hpoint.tendsto.sub_const (G t x)).norm.pow 2)
  have hsq : Tendsto (fun s => ‖metricEntropyGradientLp (F.metric s) hη hc Q u -
      metricEntropyGradientLp (F.metric t) hη hc Q u‖ ^ 2) (𝓝[I] t) (𝓝 0) := by
    simpa only [G, metricEntropyGradientLp_difference_integral
      (F.metric _) (F.metric t) hη hc Q u, integral_zero] using hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

end PoincareConjecture.M35.Uniqueness.Heat
