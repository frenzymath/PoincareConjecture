import PoincareConjecture.Proofs.M35.CapGeometry.RetainedCurvatureDerivativeBall
import PoincareConjecture.Proofs.M35.CapGeometry.RadialDerivativeBall
import PoincareConjecture.Proofs.M35.CapGeometry.FarTipSlope
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCurvatureDrop










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single (2 : Fin 3) 1




theorem blowupSequence_far_tip_radial_sectional_tendsto_zero
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    let G k := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k)))
      ((blowupSequence P E t x ht hR).scale (L.subsequence k))
      ((blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k))
    Tendsto (fun k => radialMixedCurvatureFactor (G k) ‖x (L.subsequence k)‖ /
      axisRadialCoefficient (G k) ‖x (L.subsequence k)‖) atTop (𝓝 0) := by
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let hQ k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G k := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
  let D k := M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k))) (Q k) (hQ k)
  let a k := ‖x (L.subsequence k)‖
  change Tendsto (fun k => radialMixedCurvatureFactor (G k) (a k) /
    axisRadialCoefficient (G k) (a k)) atTop (𝓝 0)
  have hrotation (k : ℕ) := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence k)) (ht (L.subsequence k))) (Q k) (hQ k)
  have hsec (k : ℕ) : (D k).NonnegativeSectionalCurvature :=
    scaleLeviCivitaData_nonnegative_sectional _
      (E.nonnegative_sectional (t (L.subsequence k)) (ht (L.subsequence k))) (Q k) (hQ k)
  have hcomplete (k : ℕ) : MetricComplete (G k) := scaleSmoothMetric_complete _
    (E.complete (t (L.subsequence k)) (ht (L.subsequence k))) (Q k) (hQ k)
  have hindex := L.subsequence_strictMono.tendsto_atTop
  have hxne : ∀ᶠ k in atTop, x (L.subsequence k) ≠ 0 := by
    filter_upwards [(hd.comp hindex).eventually (eventually_gt_atTop 0)] with k hk
    intro heq
    have hzero : (E.flow.metric (t (L.subsequence k))).edist 0 (x (L.subsequence k)) = 0 := by
      rw [heq]
      exact @edist_self StandardCapSpace
        (E.flow.metric (t (L.subsequence k))).toEMetricSpace.toPseudoEMetricSpace 0
    have hfalse := hk
    simp only [Function.comp_apply, hzero, ENNReal.toReal_zero, zero_mul,
      lt_self_iff_false] at hfalse
  have hapos : ∀ᶠ k in atTop, 0 < a k := hxne.mono (fun _ hk => norm_pos_iff.mpr hk)
  have hslopeOriginal := (E.axisWarpingSlope_tendsto_zero_of_normalized_distance
    P t x ht hR hd).comp hindex
  have hslope : Tendsto (fun k => axisWarpingSlope (G k) (a k)) atTop (𝓝 0) := by
    apply hslopeOriginal.congr'
    filter_upwards [hapos] with k hk
    exact (axisWarpingSlope_scale _ (Q k) (hQ k) hk).symm
  have hradius : ∀ᶠ k in atTop, 1 ≤ axisWarpingRadius (G k) (a k) := by
    filter_upwards [hxne,
      hslopeOriginal.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with k hk hsmall
    have hnonneg := axisWarpingSlope_nonneg (E.flow.connection (t (L.subsequence k)))
      (E.rotation_invariant (t (L.subsequence k)) (ht (L.subsequence k)))
      (E.nonnegative_sectional (t (L.subsequence k)) (ht (L.subsequence k)))
      (E.complete (t (L.subsequence k)) (ht (L.subsequence k))) (norm_pos_iff.mpr hk)
    have hsmall' : axisWarpingSlope (E.flow.metric (t (L.subsequence k))) (a k) ^ 2 ≤ 1 / 2 := by
      dsimp only [Function.comp_apply] at hsmall
      nlinarith
    have h := E.one_le_normalized_orbit_radius_of_slope_small P (ht (L.subsequence k)) hk hsmall'
    change 1 ≤ axisWarpingRadius
      (M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)) (a k)
    rw [axisWarpingRadius_scale]
    dsimp only [Q]
    rw [blowupSequence_scale]
    simpa only [mul_comm] using h
  obtain ⟨d, B, hdpos, hB, hball⟩ :=
    blowupSequence_exists_curvature_derivative_ball_bound P E t x ht hR L
  have hbound : ∀ᶠ k in atTop, ∀ r, a k ≤ r →
      radialArclength (G k) r - radialArclength (G k) (a k) ≤ d / 2 →
        (D k).curvatureDerivativeNorm 1 (r • e2) ≤ B := by
    filter_upwards [hball] with k hk r hr hlength
    exact radial_curvatureDerivative_bound_of_ball_bound (D k) (hrotation k)
      hdpos (x (L.subsequence k)) hk hr hlength
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [hapos] with k hk
    exact hb.trans_le
      (div_nonneg (radialMixedCurvatureFactor_nonneg (D k) (hrotation k) (hsec k) hk)
        (axisRadialCoefficient_pos (G k) (a k)).le)
  · intro ε hε
    let ell := min (d / 2) (ε / (2 * B))
    have hell : 0 < ell := lt_min (half_pos hdpos) (by positivity)
    have helld : ell ≤ d / 2 := min_le_left _ _
    have hBell : B * ell ≤ ε / 2 := by
      have h := (le_div_iff₀ (show 0 < 2 * B by positivity)).mp
        (min_le_right (d / 2) (ε / (2 * B)))
      dsimp only [ell]
      linarith
    have hδ : 0 < (ε / 2) * ell := mul_pos (half_pos hε) hell
    filter_upwards [hapos, hradius, hbound,
      hslope.eventually (eventually_lt_nhds hδ)] with k hk hρk hboundk hslopek
    by_contra hbad
    obtain ⟨b, hab, hlength⟩ := exists_outward_radial_interval (G k) (hcomplete k) hk.le hell
    have hbnd (r : ℝ) (hr : r ∈ Icc (a k) b) :
        (D k).curvatureDerivativeNorm 1 (r • e2) ≤ B := by
      apply hboundk r hr.1
      have hs := (radialArclength_strictMono (G k)).monotone hr.2
      linarith
    have hdrop := radialMixedSectional_slope_drop (D k)
      (P.curvature.tensor_calculus 3 StandardCapSpace (G k) (D k)) (hrotation k)
      (hsec k) (hcomplete k) hk hab.le hB.le hε hbnd (le_of_not_gt hbad)
      (by rw [hlength]; exact hBell)
    rw [hlength] at hdrop
    have hρmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hρk (half_pos hε).le) hell.le
    nlinarith only [hρmul, hdrop, hslopek]

end PoincareConjecture.M35.OrdinaryRealization
