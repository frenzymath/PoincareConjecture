import PoincareConjecture.Proofs.M35.CapGeometry.CoreBallVolume











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness



theorem exists_selected_core_volume_constant
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t Q : ℕ → ℝ)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hQ : ∀ k, 0 < Q k)
    (htone : Tendsto t atTop (𝓝 1)) (hQtop : Tendsto Q atTop atTop)
    (F : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ k in atTop, ∀ C ≥ C₀,
      ∀ y : StandardCapSpace, ∀ r : ℝ, 0 < r →
        r * Real.sqrt (Q k) ≤ F →
        scalarCurvatureSupOn (E.flow.metric (t k)) (E.flow.connection (t k))
          ((E.flow.metric (t k)).ball y r) = r⁻¹ ^ 2 →
        ENNReal.ofReal (C⁻¹ * r ^ 3) <
          calibratedMetricVolume (E.flow.metric (t k)) ((E.flow.metric (t k)).ball y r) := by
  obtain ⟨NC⟩ := E.noncollapsing
  have hcorelim : Tendsto (fun k => F / Real.sqrt (Q k)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp hQtop).const_div_atTop F
  let C₀ := 16 / NC.kappa + 1
  have hC₀ : 0 < C₀ := by
    have hk := NC.kappa_pos
    dsimp only [C₀]
    positivity
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hcorelim.eventually (eventually_lt_nhds NC.radius_pos),
    hcorelim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    htone.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
    with k hsmall hhalf htime
  intro C hC y r hr hrbound hrscale
  have hrupper : r ≤ F / Real.sqrt (Q k) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr (hQ k))).mpr hrbound
  have hCpos : 0 < C := hC₀.trans_le hC
  have hCinv : C⁻¹ < NC.kappa / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hC NC.kappa_pos.le
    dsimp only [C₀] at hmul
    rw [mul_add, mul_div_cancel₀ 16 NC.kappa_pos.ne', mul_one] at hmul
    apply (inv_lt_iff_one_lt_mul₀ hCpos).mpr
    nlinarith only [hmul, NC.kappa_pos]
  have hrsq : r ^ 2 ≤ t k := by
    have h := pow_le_pow_left₀ hr.le (hrupper.trans hhalf.le) 2
    norm_num at h
    linarith only [h, htime]
  have hvolume := E.scalar_curvature_ball_volume_lower P.curvature NC (ht k) hr
    (hrupper.trans hsmall.le) hrsq y hrscale
  apply lt_of_lt_of_le _ hvolume
  have hk := NC.kappa_pos
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < NC.kappa / 8 * r ^ 3)).mpr
    (mul_lt_mul_of_pos_right hCinv (pow_pos hr 3))

end PoincareConjecture.M35.Uniqueness
