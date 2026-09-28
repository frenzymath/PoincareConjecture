import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_StandardPoleSmooth










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M44

open M36 RiemannianMetric



theorem standardRadialExponential_image_tangent_ball (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    standardRadialExponential g₀ '' {v | g₀.metric.tangentNorm 0 v < r} =
      g₀.metric.ball 0 r := by
  have hcompact : IsCompact (closure (g₀.metric.ball 0 r)) := by
    rw [standard_closure_ball g₀ hr]
    exact standard_closed_ball_compact g₀ hr.le
  obtain ⟨e, _, _, _, hexp, _, hballs⟩ :=
    g₀.metric.exists_smooth_exponential_with_ball_images 0 hr hcompact
  have heq := standard_exponential_eq_radial g₀ hexp
  rw [← hballs r hr le_rfl]
  exact Set.image_congr (fun _ hv => (heq hv).symm)



theorem standardRadialExponential_radial_edist (g₀ : StandardInitialMetric)
    (v : StandardCapSpace) :
    g₀.metric.edist 0 (standardRadialExponential g₀ v) =
      ENNReal.ofReal (g₀.metric.tangentNorm 0 v) := by
  let R := g₀.metric.tangentNorm 0 v + 1
  have hR : 0 < R := by
    dsimp only [R, tangentNorm]
    linarith [Real.sqrt_nonneg (g₀.metric.inner 0 v v)]
  have hcompact : IsCompact (closure (g₀.metric.ball 0 R)) := by
    rw [standard_closure_ball g₀ hR]
    exact standard_closed_ball_compact g₀ hR.le
  obtain ⟨e, _, _, _, hexp, hbound, _⟩ :=
    g₀.metric.exists_smooth_exponential_with_ball_images 0 hR hcompact
  have heq := standard_exponential_eq_radial g₀ hexp
  have hv : g₀.metric.tangentNorm 0 v < R := by dsimp only [R]; linarith
  have hinj : InjOn e {w | g₀.metric.tangentNorm 0 w < R} := by
    intro a ha b hb hab
    apply standardRadialExponential_injective g₀
    rw [← heq ha, ← heq hb]
    exact hab
  rw [← heq hv]
  exact g₀.metric.exponential_radial_edist_of_injective 0 hR hcompact e hexp hbound hinj hv



theorem standard_tangentNorm_zero (g₀ : StandardInitialMetric) (v : StandardCapSpace) :
    g₀.metric.tangentNorm 0 v = radialSpeed g₀ 0 * ‖v‖ := by
  have h := standardRadialExponential_radial_edist g₀ v
  rw [standard_edist_zero, norm_standardRadialExponential,
    radialArclength_euclideanRadius] at h
  exact ((ENNReal.ofReal_eq_ofReal_iff
    (mul_nonneg (radialSpeed_pos g₀ 0).le (norm_nonneg v)) (Real.sqrt_nonneg _)).mp h).symm



theorem standardRadialLogarithm_tangentNorm (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) :
    g₀.metric.tangentNorm 0 (standardRadialLogarithm g₀ x) =
      radialArclength g₀ ‖x‖ := by
  rw [standard_tangentNorm_zero, norm_standardRadialLogarithm,
    mul_div_cancel₀ _ (radialSpeed_pos g₀ 0).ne']



theorem standardRadialLogarithm_image_ball (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    standardRadialLogarithm g₀ '' g₀.metric.ball 0 r =
      {v | g₀.metric.tangentNorm 0 v < r} := by
  rw [← standardRadialExponential_image_tangent_ball g₀ hr, image_image]
  simp only [standardRadialLogarithm_exponential, image_id']
  rfl

end PoincareConjecture.M44
