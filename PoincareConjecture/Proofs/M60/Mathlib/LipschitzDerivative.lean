import PoincareConjecture.Proofs.M40.Mathlib.SmoothChartDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle NNReal

namespace PoincareConjecture.M60

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, F) : M → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : M → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

theorem norm_mfderiv_apply_le_of_lipschitzOn {f : E → M} {S : Set E}
    (hS : IsOpen S) {K : ℝ≥0} (hf : LipschitzOnWith K f S)
    {z : E} (hz : z ∈ S) (v : E) :
    ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z v‖ ≤ (2 * (K : ℝ)) * ‖v‖ := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f z
  · let e := chartAt F (f z)
    have he : e.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) := mdifferentiable_chart (f z)
    have hx : f z ∈ e.source := mem_chart_source F (f z)
    let n := M40.normalizedSmoothChart e he hx
    have hn : f z ∈ n.source := by
      simpa only [n, M40.normalizedSmoothChart_source] using hx
    have hns : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, TangentSpace 𝓘(ℝ, F) (f z)) ∞ n n.source :=
      M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart
    obtain ⟨R, hR, _, _, hLip⟩ :=
      M40.normalizedSmoothChart_exists_lipschitz_ball e he hx
        contMDiffOn_chart contMDiffOn_chart_symm 2 (by norm_num)
    have hN : n.symm '' Metric.ball (n (f z)) R ∈ 𝓝 (f z) := by
      simpa only [n.left_inv hn] using
        n.symm.image_mem_nhds (n.map_source hn) (Metric.ball_mem_nhds _ hR)
    let U := S ∩ f ⁻¹' (n.symm '' Metric.ball (n (f z)) R)
    have hU : U ∈ 𝓝 z := inter_mem (hS.mem_nhds hz)
      (hd.continuousAt.preimage_mem_nhds hN)
    have hcomp : LipschitzOnWith (2 * K) (n ∘ f) U :=
      hLip.comp (hf.mono inter_subset_left) (fun _ hu => hu.2)
    have hbound := norm_fderiv_le_of_lipschitzOn ℝ hU hcomp
    have hnd := (hns.contMDiffAt (n.open_source.mem_nhds hn)).mdifferentiableAt
      (by norm_num)
    have hchain : fderiv ℝ (n ∘ f) z v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z v := by
      have hc := M40.normalizedSmoothChart_mfderiv_apply e he hx
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z v)
      rw [← mfderiv_comp_apply z hnd hd, mfderiv_eq_fderiv] at hc
      exact hc
    rw [← hchain]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  · rw [mfderiv_zero_of_not_mdifferentiableAt hd]
    erw [zero_apply, norm_zero]
    positivity

end PoincareConjecture.M60
