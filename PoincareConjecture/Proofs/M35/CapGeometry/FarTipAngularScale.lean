import PoincareConjecture.Proofs.M35.CapGeometry.ActualFarTipRadialCurvature











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single (2 : Fin 3) 1



theorem blowupSequence_far_tip_normalized_orbit_sq_tendsto_two
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    Tendsto (fun k => (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (x (L.subsequence k)) *
        axisWarpingRadius (E.flow.metric (t (L.subsequence k))) ‖x (L.subsequence k)‖ ^ 2)
      atTop (𝓝 2) := by
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ (k : ℕ) : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G k := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
  let D k := M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k))) (Q k) (hQ k)
  let r k := ‖x (L.subsequence k)‖
  let f k := axisWarpingRadius (G k) (r k)
  let u k := axisWarpingSlope (G k) (r k)
  let K k := radialMixedCurvatureFactor (G k) (r k) / axisRadialCoefficient (G k) (r k)
  have hrotation (k : ℕ) := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence k)) (ht (L.subsequence k))) (Q k) (hQ k)
  have hindex := L.subsequence_strictMono.tendsto_atTop
  have hr : ∀ᶠ k in atTop, 0 < r k := by
    filter_upwards [(hd.comp hindex).eventually (eventually_gt_atTop 0)] with k hk
    apply norm_pos_iff.mpr
    intro hx
    have hz : (E.flow.metric (t (L.subsequence k))).edist 0 (x (L.subsequence k)) = 0 := by
      rw [hx]
      exact @edist_self StandardCapSpace
        (E.flow.metric (t (L.subsequence k))).toEMetricSpace.toPseudoEMetricSpace 0
    simp only [Function.comp_apply, hz, ENNReal.toReal_zero, zero_mul,
      lt_self_iff_false] at hk
  have hu : Tendsto u atTop (𝓝 0) := by
    apply ((E.axisWarpingSlope_tendsto_zero_of_normalized_distance P t x ht hR hd).comp
      hindex).congr'
    filter_upwards [hr] with k hk
    exact (axisWarpingSlope_scale _ (Q k) (hQ k) hk).symm
  have hK : Tendsto K atTop (𝓝 0) :=
    blowupSequence_far_tip_radial_sectional_tendsto_zero P E t x ht hR hd L
  have hscalar (k : ℕ) : (D k).scalarCurvature (r k • e2) = 1 := by
    have hs := M13.homothety_scalarCurvature_eq
      (E.flow.metric (t (L.subsequence k))) (G k)
      (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) (Q k) (hQ k)
      (M13.identity_metricHomothety _ (Q k) (hQ k))
      (E.flow.connection (t (L.subsequence k))) (D k) (x (L.subsequence k))
    change (D k).scalarCurvature (x (L.subsequence k)) =
      (E.flow.connection (t (L.subsequence k))).scalarCurvature (x (L.subsequence k)) /
        Q k at hs
    have hvalue : (D k).scalarCurvature (x (L.subsequence k)) = 1 := by
      apply hs.trans
      rw [show Q k = (E.flow.connection (t (L.subsequence k))).scalarCurvature
        (x (L.subsequence k)) from blowupSequence_scale P E t x ht hR (L.subsequence k)]
      exact div_self (E.scalar_pos (ht (L.subsequence k)) (x (L.subsequence k))).ne'
    exact (rotational_scalar_edist_eq_axis P (D k) (hrotation k)
      (x (L.subsequence k))).1.symm.trans hvalue
  have hden : Tendsto (fun k => 1 - 4 * K k) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hK.const_mul 4)
  have hformula : ∀ᶠ k in atTop, f k ^ 2 = 2 * (1 - u k ^ 2) / (1 - 4 * K k) := by
    filter_upwards [hr, hden.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))]
      with k hk hne
    have hs : (1 : ℝ) = 2 * ((1 - u k ^ 2) / f k ^ 2) + 4 * K k := by
      calc
        1 = 2 * radialTangentialCurvatureFactor (G k) (r k) /
            axisAngularCoefficient (G k) (r k) + 4 * K k := by
          rw [← hscalar k, rotational_scalar_axis (D k) (hrotation k) hk]
          dsimp only [K]
          ring
        _ = _ := by
          rw [show 2 * radialTangentialCurvatureFactor (G k) (r k) /
              axisAngularCoefficient (G k) (r k) =
              2 * (radialTangentialCurvatureFactor (G k) (r k) /
                axisAngularCoefficient (G k) (r k)) by ring,
            radialTangentialCurvatureFactor_eq_warping (G k) hk]
    have hquot : 1 - 4 * K k = (2 * (1 - u k ^ 2)) / f k ^ 2 := by
      calc
        _ = 2 * ((1 - u k ^ 2) / f k ^ 2) := by linarith only [hs]
        _ = _ := by ring
    have hmul := (eq_div_iff (pow_ne_zero 2 (axisWarpingRadius_pos (G k) hk).ne')).mp hquot
    apply (eq_div_iff hne).mpr
    simpa only [mul_comm] using hmul
  have hf : Tendsto (fun k => f k ^ 2) atTop (𝓝 2) := by
    have hnum : Tendsto (fun k => 2 * (1 - u k ^ 2)) atTop (𝓝 2) := by
      simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), sub_zero, mul_one] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (hu.pow 2)).const_mul 2
    have hdiv : Tendsto (fun k => 2 * (1 - u k ^ 2) / (1 - 4 * K k))
        atTop (𝓝 2) := by
      convert! hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
      simp only [div_one]
    exact hdiv.congr' (hformula.mono fun _ h => h.symm)
  apply hf.congr'
  filter_upwards [] with k
  change axisWarpingRadius (M13.scaleSmoothMetric _ (Q k) (hQ k)) (r k) ^ 2 = _
  rw [axisWarpingRadius_scale, mul_pow, Real.sq_sqrt (hQ k).le]
  rw [show Q k = (E.flow.connection (t (L.subsequence k))).scalarCurvature
    (x (L.subsequence k)) from blowupSequence_scale P E t x ht hR (L.subsequence k)]

end PoincareConjecture.M35.OrdinaryRealization
