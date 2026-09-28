import PoincareConjecture.Proofs.M60.Mathlib.DerivativeKernel
import PoincareConjecture.Proofs.M40.Mathlib.SmoothChartDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle NNReal ENNReal

namespace PoincareConjecture.M60

variable {E F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, F) : M → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : M → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

theorem mfderiv_apply_eq_zero_of_increment_bound {f : E → G} {h : E → M}
    {x : E} {C : ℝ≥0} (hf : DifferentiableAt ℝ f x)
    (hbound : ∀ᶠ y in 𝓝 x, edist (h y) (h x) ≤ C * ENNReal.ofReal ‖f y - f x‖)
    {v : E} (hv : fderiv ℝ f x v = 0) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) h x v = 0 := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) h x
  · let e := chartAt F (h x)
    have he : e.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) := mdifferentiable_chart (h x)
    have hx : h x ∈ e.source := mem_chart_source F (h x)
    let n := M40.normalizedSmoothChart e he hx
    have hn : h x ∈ n.source := by
      simpa only [n, M40.normalizedSmoothChart_source] using hx
    have hns : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, TangentSpace 𝓘(ℝ, F) (h x)) ∞ n n.source :=
      M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart
    obtain ⟨R, hR, _, _, hLip⟩ := M40.normalizedSmoothChart_exists_lipschitz_ball
      e he hx contMDiffOn_chart contMDiffOn_chart_symm 2 (by norm_num)
    have hN : n.symm '' Metric.ball (n (h x)) R ∈ 𝓝 (h x) := by
      simpa only [n.left_inv hn] using
        n.symm.image_mem_nhds (n.map_source hn) (Metric.ball_mem_nhds _ hR)
    have hb : ∀ᶠ y in 𝓝 x, ‖(n ∘ h) y - (n ∘ h) x‖ ≤
        (2 * (C : ℝ)) * ‖f y - f x‖ := by
      filter_upwards [hbound, hd.continuousAt.preimage_mem_nhds hN] with y hy hyN
      have hmul : (2 : ℝ≥0∞) * edist (h y) (h x) ≤
          2 * (C * ENNReal.ofReal ‖f y - f x‖) := by gcongr
      have hedist := (hLip hyN (mem_of_mem_nhds hN)).trans hmul
      have hedist' : ENNReal.ofReal ‖(n ∘ h) y - (n ∘ h) x‖ ≤
          ENNReal.ofReal ((2 * (C : ℝ)) * ‖f y - f x‖) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) C.coe_nonneg),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_coe_nnreal, mul_assoc]
        simpa only [edist_dist, dist_eq_norm, Function.comp_apply,
          ENNReal.coe_ofNat] using hedist
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hedist'
    have hnd := (hns.contMDiffAt (n.open_source.mem_nhds hn)).mdifferentiableAt
      (by norm_num)
    have hchain : fderiv ℝ (n ∘ h) x v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) h x v := by
      have hc := M40.normalizedSmoothChart_mfderiv_apply e he hx
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) h x v)
      rw [← mfderiv_comp_apply x hnd hd, mfderiv_eq_fderiv] at hc
      exact hc
    rw [← hchain]
    exact fderiv_apply_eq_zero_of_increment_bound hf hb hv
  · rw [mfderiv_zero_of_not_mdifferentiableAt hd]
    exact zero_apply _

end PoincareConjecture.M60
