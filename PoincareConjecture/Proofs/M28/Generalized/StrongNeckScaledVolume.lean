import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceNeck
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeLower
import PoincareConjecture.Proofs.M28.Generalized.MetricVolumeCalibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

def strongNeckNoncollapseConstant : ℝ := normalizedNeckVolumeLowerConstant / 16 ^ 3

theorem strongNeckNoncollapseConstant_pos : 0 < strongNeckNoncollapseConstant :=
  div_pos normalizedNeckVolumeLowerConstant_pos (by norm_num)

theorem GeneralizedStrongNeck.scaled_ambient_ball_volume_lower
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (J : GeneralizedStrongNeck F t epsilon) (Q : ℝ) (hQ : 0 < Q)
    (hsmall : epsilon ≤ (1 / 200 : ℝ)) {r : ℝ} (hr : 0 < r)
    (hrscale : r ≤ 2 * (Real.sqrt Q * J.scale)) :
    let G : RiemannianMetric 3 (F.slice t).carrier :=
      M13.scaleSmoothMetric (F.metric t) Q hQ
    ENNReal.ofReal (strongNeckNoncollapseConstant * r ^ 3) ≤
      G.volumeMeasure (G.ball J.center r) := by
  obtain ⟨H⟩ := GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow J
  let W := strongNeckOpen J
  let G : RiemannianMetric 3 (F.slice t).carrier :=
    M13.scaleSmoothMetric (F.metric t) Q hQ
  let gN : RiemannianMetric 3 W := H.rescaling.flow.metric 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : W → Type _) :=
    ⟨gN.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : W → Type _) :=
    ⟨⟨gN.inner, gN.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace W := EMetricSpace.ofRiemannianMetric (𝓡 3) W
  let gW := intrinsicOpenMetric G W
  let p := strongNeckSourceCenter J
  let s := Real.sqrt Q * J.scale
  have hs : 0 < s := mul_pos (Real.sqrt_pos.mpr hQ) J.scale_pos
  let δ := (r / 16) / s
  have hδ : 0 < δ := div_pos (div_pos hr (by norm_num)) hs
  have hδsmall : δ ≤ 1 / 8 := by
    apply (div_le_iff₀ hs).mpr
    linarith only [hrscale]
  have hsδ : s * δ = r / 16 := by
    dsimp only [δ]
    rw [mul_comm, div_mul_cancel₀ _ hs.ne']
  have hhalf : epsilon < 1 / 2 := hsmall.trans_lt (by norm_num)
  let N := GeneralizedStrongNeck.rescaled_source_neck J hhalf H
  have hA : (200 : ℝ) ≤ epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hsmall (inv_pos.mpr J.epsilon_pos).le
    rw [mul_inv_cancel₀ J.epsilon_pos.ne'] at h
    linarith only [h]
  have hbuffer : (1 : ℝ) ≤ N.epsilon⁻¹ / 16 := by
    change (1 : ℝ) ≤ epsilon⁻¹ / 16
    linarith only [hA]
  have hp : p ∈ gN.ball N.center 1 := by
    change gN.edist p p < ENNReal.ofReal 1
    have hself : gN.edist p p = 0 := by
      exact @edist_self W (inferInstance : PseudoEMetricSpace W) p
    rw [hself]
    exact ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1)
  have hvolume := normalized_neck_ball_volume_lower N rfl rfl hsmall
    (by norm_num : (0 : ℝ) < 1) hbuffer hp hδ hδsmall
  have hmetric : MetricHomothety gN gW (Diffeomorph.refl (𝓡 3) W ∞) (s ^ 2) := by
    intro x v w
    rw [Diffeomorph.coe_refl]
    change gW.inner x (mfderiv (𝓡 3) (𝓡 3) (id : W → W) x v)
      (mfderiv (𝓡 3) (𝓡 3) (id : W → W) x w) = s ^ 2 * gN.inner x v w
    rw [mfderiv_id]
    change gW.inner x v w = s ^ 2 * gN.inner x v w
    rw [intrinsicOpenMetric_inner, M13.scaleSmoothMetric_inner,
      GeneralizedStrongNeck.rescaled_metric_at_zero J H x v w]
    dsimp only [s]
    rw [mul_pow, Real.sq_sqrt hQ.le]
    have hcancel : J.scale ^ 2 * J.scale⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ J.scale_pos.ne', one_pow]
    calc
      _ = Q * (J.scale ^ 2 * J.scale⁻¹ ^ 2) *
          (F.metric t).inner (x : (F.slice t).carrier)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → (F.slice t).carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → (F.slice t).carrier) x w) := by
        rw [hcancel, mul_one]
      _ = _ := by ring
  have hradius : Real.sqrt (s ^ 2) * δ = r / 16 := by
    rw [Real.sqrt_sq hs.le, hsδ]
  have hball : gW.ball p (r / 16) = gN.ball p δ := by
    have h := M13.homothety_ball_image gN gW (Diffeomorph.refl (𝓡 3) W ∞)
      (s ^ 2) (sq_pos_of_pos hs) hmetric p δ
    rw [hradius] at h
    rw [Diffeomorph.coe_refl, Set.image_id] at h
    exact h.symm
  have hfactor : Real.rpow (s ^ 2) ((3 : ℝ) / 2) = s ^ (3 : ℕ) := by
    change (s ^ 2) ^ ((3 : ℝ) / 2) = _
    rw [Real.rpow_div_two_eq_sqrt _ (sq_nonneg s), Real.rpow_ofNat]
    rw [Real.sqrt_sq hs.le]
  have hvolscale : gW.volumeMeasure (gN.ball p δ) =
      ENNReal.ofReal (s ^ (3 : ℕ)) * gN.volumeMeasure (gN.ball p δ) := by
    have h := volumeMeasure_homothety_image gN gW (Diffeomorph.refl (𝓡 3) W ∞)
      (s ^ 2) (sq_pos_of_pos hs) hmetric (gN.ball p δ)
    norm_num only [Nat.cast_ofNat] at h
    simpa only [Diffeomorph.coe_refl, Set.image_id, hfactor] using h
  have hscaled : ENNReal.ofReal (strongNeckNoncollapseConstant * r ^ 3) ≤
      gW.volumeMeasure (gW.ball p (r / 16)) := by
    rw [hball, hvolscale]
    calc
      _ = ENNReal.ofReal (s ^ (3 : ℕ)) *
          ENNReal.ofReal (normalizedNeckVolumeLowerConstant * δ ^ 3) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hs.le 3)]
        congr 1
        calc
          _ = normalizedNeckVolumeLowerConstant * (r / 16) ^ 3 := by
            dsimp only [strongNeckNoncollapseConstant]
            ring
          _ = normalizedNeckVolumeLowerConstant * (s * δ) ^ 3 := by rw [hsδ]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_right hvolume _
  have hmeas : MeasurableSet (gW.ball p (r / 16)) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : W → Type _) :=
      ⟨gW.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : W → Type _) :=
      ⟨⟨gW.inner, gW.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace W := EMetricSpace.ofRiemannianMetric (𝓡 3) W
    change MeasurableSet {x : W | edist p x < ENNReal.ofReal (r / 16)}
    exact (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  have himage : (Subtype.val : W → (F.slice t).carrier) '' gW.ball p (r / 16) ⊆
      G.ball J.center r := by
    rintro _ ⟨x, hx, rfl⟩
    have hdist := RiemannianMetric.edist_le_intrinsicEDist G W (p : _) (x : _)
    rw [← intrinsicOpenMetric_edist] at hdist
    exact (hdist.trans_lt hx).trans_le (ENNReal.ofReal_le_ofReal (by linarith : r / 16 ≤ r))
  change ENNReal.ofReal (strongNeckNoncollapseConstant * r ^ 3) ≤
    G.volumeMeasure (G.ball J.center r)
  rw [intrinsicOpenMetric_volumeMeasure_apply G W hmeas] at hscaled
  exact hscaled.trans (measure_mono himage)

end PoincareConjecture.M28
