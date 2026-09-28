import PoincareConjecture.Proofs.M35.CapGeometry.RadialPointIdentification










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RepairedStandardCapExistenceData

open M35.Uniqueness



theorem axisWarpingSlope_tendsto_zero_of_normalized_arclength
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hs : Tendsto (fun k => radialArclength (E.flow.metric (t k)) ‖x k‖ *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop) :
    Tendsto (fun k => axisWarpingSlope (E.flow.metric (t k)) ‖x k‖) atTop (𝓝 0) := by
  obtain ⟨B, H, _hB, _hH, hbound⟩ := E.exists_normalized_orbit_radius_bound_all_points P
  let s (k : ℕ) := radialArclength (E.flow.metric (t k)) ‖x k‖ *
    Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))
  have hspos : ∀ᶠ k in atTop, 0 < s k := hs.eventually (eventually_gt_atTop 0)
  have hxne : ∀ᶠ k in atTop, x k ≠ 0 := by
    filter_upwards [hspos] with k hk
    intro heq
    have hfalse := hk
    simp only [s, heq, norm_zero, radialArclength_zero, zero_mul, lt_self_iff_false] at hfalse
  have hnonneg : ∀ᶠ k in atTop, 0 ≤ axisWarpingSlope (E.flow.metric (t k)) ‖x k‖ := by
    filter_upwards [hxne] with k hk
    exact axisWarpingSlope_nonneg (E.flow.connection (t k)) (E.rotation_invariant (t k) (ht k))
      (E.nonnegative_sectional (t k) (ht k)) (E.complete (t k) (ht k)) (norm_pos_iff.mpr hk)
  have hupper : ∀ᶠ k in atTop,
      axisWarpingSlope (E.flow.metric (t k)) ‖x k‖ ≤ B / s k := by
    filter_upwards [hxne, hspos, hR.eventually (eventually_ge_atTop H)] with k hk hsk hRk
    have h := mul_le_mul_of_nonneg_right
      (axisWarpingSlope_mul_arclength_le (E.flow.connection (t k))
        (E.rotation_invariant (t k) (ht k)) (E.nonnegative_sectional (t k) (ht k))
        (norm_pos_iff.mpr hk))
      (Real.sqrt_nonneg ((E.flow.connection (t k)).scalarCurvature (x k)))
    apply (le_div_iff₀ hsk).mpr
    calc
      _ = (axisWarpingSlope (E.flow.metric (t k)) ‖x k‖ *
          radialArclength (E.flow.metric (t k)) ‖x k‖) *
            Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)) := by
        dsimp only [s]
        ring
      _ ≤ _ := h
      _ ≤ B := hbound (t k) (ht k) (x k) hk hRk
  exact squeeze_zero' hnonneg hupper (tendsto_const_nhds.div_atTop hs)



theorem axisWarpingSlope_tendsto_zero_of_normalized_distance
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop) :
    Tendsto (fun k => axisWarpingSlope (E.flow.metric (t k)) ‖x k‖) atTop (𝓝 0) := by
  apply E.axisWarpingSlope_tendsto_zero_of_normalized_arclength P t x ht hR
  apply tendsto_atTop_mono _ hd
  intro k
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hs : 0 ≤ radialArclength (E.flow.metric (t k)) ‖x k‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono (E.flow.metric (t k))).monotone (norm_nonneg (x k))
  apply ENNReal.toReal_le_of_le_ofReal hs
  rw [(rotational_scalar_edist_eq_axis P (E.flow.connection (t k))
    (E.rotation_invariant (t k) (ht k)) (x k)).2]
  exact edist_axis_le_radialArclength (E.flow.metric (t k)) (norm_nonneg (x k))



theorem one_le_normalized_orbit_radius_of_slope_small
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {t : ℝ}
    (ht : t ∈ Ico 0 E.flow.base.lifetime) {x : StandardCapSpace} (hx : x ≠ 0)
    (hsmall : axisWarpingSlope (E.flow.metric t) ‖x‖ ^ 2 ≤ 1 / 2) :
    1 ≤ axisWarpingRadius (E.flow.metric t) ‖x‖ *
      Real.sqrt ((E.flow.connection t).scalarCurvature x) := by
  have hr := norm_pos_iff.mpr hx
  have h := scalar_mul_axisWarpingRadius_sq_ge (E.flow.connection t)
    (E.rotation_invariant t ht) (E.nonnegative_sectional t ht) hr
  have hs := (rotational_scalar_edist_eq_axis P (E.flow.connection t)
    (E.rotation_invariant t ht) x).1
  rw [← hs] at h
  apply le_of_sq_le_sq _
    (mul_nonneg (axisWarpingRadius_pos (E.flow.metric t) hr).le (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt (E.scalar_pos ht x).le]
  nlinarith



theorem axisWarpingSlope_div_normalized_radius_tendsto_zero
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop) :
    Tendsto (fun k => axisWarpingSlope (E.flow.metric (t k)) ‖x k‖ /
      (axisWarpingRadius (E.flow.metric (t k)) ‖x k‖ *
        Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)))) atTop (𝓝 0) := by
  have hu := E.axisWarpingSlope_tendsto_zero_of_normalized_distance P t x ht hR hd
  have hxne : ∀ᶠ k in atTop, x k ≠ 0 := by
    filter_upwards [hd.eventually (eventually_gt_atTop 0)] with k hk
    intro heq
    have hzero : (E.flow.metric (t k)).edist 0 (x k) = 0 := by
      rw [heq]
      exact @edist_self StandardCapSpace (E.flow.metric (t k)).toEMetricSpace.toPseudoEMetricSpace 0
    have hfalse := hk
    simp only [hzero, ENNReal.toReal_zero, zero_mul, lt_self_iff_false] at hfalse
  have hb : ∀ᶠ k in atTop,
      0 ≤ axisWarpingSlope (E.flow.metric (t k)) ‖x k‖ ∧
      1 ≤ axisWarpingRadius (E.flow.metric (t k)) ‖x k‖ *
        Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)) := by
    filter_upwards [hxne, hu.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with k hk hsmall
    have hnonneg := axisWarpingSlope_nonneg (E.flow.connection (t k))
      (E.rotation_invariant (t k) (ht k)) (E.nonnegative_sectional (t k) (ht k))
      (E.complete (t k) (ht k)) (norm_pos_iff.mpr hk)
    refine ⟨hnonneg, E.one_le_normalized_orbit_radius_of_slope_small P (ht k) hk ?_⟩
    nlinarith
  apply squeeze_zero' _ _ hu
  · filter_upwards [hb] with k hk
    exact div_nonneg hk.1 (zero_le_one.trans hk.2)
  · filter_upwards [hb] with k hk
    exact div_le_self hk.1 hk.2

end PoincareConjecture.RepairedStandardCapExistenceData
