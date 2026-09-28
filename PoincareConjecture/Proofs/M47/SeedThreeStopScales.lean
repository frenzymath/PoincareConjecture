import PoincareConjecture.Proofs.M47.SeedThreeStopVolume








set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_three_stop_scales
    (S : RepairedControlledSchedulesData.{u}) (p : SurgeryParameterPrefix S.constants)
    {H B R : ℝ} (hH : 0 < H) (hB : M46.seedAnalyticConstant S ≤ B) (hR : 0 < R) :
    ∃ d r : ℝ, 0 < d ∧ 0 < r ∧ r ≤ R ∧
      64 * B * H * d ≤ 1 ∧
      6 * (13 * max (4 * H) (Real.exp 4)) * d ≤ 1 / 2 ∧
      r ≤ 1 ∧ r ≤ p.setup.epsilon ∧ (r / 4) ^ 2 ≤ d / 2 ∧
      13 * max (4 * H) (Real.exp 4) ≤ (r / 4)⁻¹ ^ 2 ∧
      2 * H * r ^ 2 ≤ 1 ∧ 3 * r ≤ (Real.sqrt (4 * H))⁻¹ / (8 * B) := by
  have hBpos : 0 < B := (M46.seedAnalyticConstant_pos S).trans_le hB
  let K := 13 * max (4 * H) (Real.exp 4)
  have hK : 0 < K := by dsimp only [K]; positivity
  let d := min (1 / (64 * B * H)) (1 / (12 * K))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdScalar := (le_div_iff₀ (by positivity : 0 < 64 * B * H)).mp
    (min_le_left (1 / (64 * B * H)) (1 / (12 * K)))
  have hdMetric := (le_div_iff₀ (by positivity : 0 < 12 * K)).mp
    (min_le_right (1 / (64 * B * H)) (1 / (12 * K)))
  change d * (64 * B * H) ≤ 1 at hdScalar
  change d * (12 * K) ≤ 1 at hdMetric
  let r := min R (min 1 (min p.setup.epsilon (min (Real.sqrt d)
    (min (Real.sqrt K)⁻¹ (min (Real.sqrt (2 * H))⁻¹
      ((Real.sqrt (4 * H))⁻¹ / (24 * B)))))))
  have hepsilon := p.setup.epsilon_pos
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrAll : r ≤ R ∧ r ≤ 1 ∧ r ≤ p.setup.epsilon ∧ r ≤ Real.sqrt d ∧
      r ≤ (Real.sqrt K)⁻¹ ∧ r ≤ (Real.sqrt (2 * H))⁻¹ ∧
        r ≤ (Real.sqrt (4 * H))⁻¹ / (24 * B) := by
    simpa only [r, le_min_iff] using (le_refl r)
  rcases hrAll with ⟨hrR, hr1, hrepsilon, hrd, hrK, hrH, hrTube⟩
  have hrdSq : r ^ 2 ≤ d := by
    simpa only [Real.sq_sqrt hd.le] using (sq_le_sq₀ hr.le (Real.sqrt_nonneg d)).mpr hrd
  have hKr : K * r ^ 2 ≤ 1 := by
    have hsquare := (sq_le_sq₀ hr.le (inv_nonneg.mpr (Real.sqrt_nonneg K))).mpr hrK
    rw [inv_pow, Real.sq_sqrt hK.le] at hsquare
    exact (mul_le_mul_of_nonneg_left hsquare hK.le).trans_eq (mul_inv_cancel₀ hK.ne')
  have hHr : 2 * H * r ^ 2 ≤ 1 := by
    have h2H : 0 < 2 * H := by positivity
    have hsquare := (sq_le_sq₀ hr.le
      (inv_nonneg.mpr (Real.sqrt_nonneg (2 * H)))).mpr hrH
    rw [inv_pow, Real.sq_sqrt h2H.le] at hsquare
    exact (mul_le_mul_of_nonneg_left hsquare h2H.le).trans_eq (mul_inv_cancel₀ h2H.ne')
  refine ⟨d, r, hd, hr, hrR, by nlinarith, by nlinarith, hr1, hrepsilon,
    by nlinarith, ?_, hHr, ?_⟩
  · change K ≤ (r / 4)⁻¹ ^ 2
    rw [inv_pow, inv_eq_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < r / 4))).mpr
    nlinarith
  · calc
      3 * r ≤ 3 * ((Real.sqrt (4 * H))⁻¹ / (24 * B)) :=
        mul_le_mul_of_nonneg_left hrTube (by norm_num)
      _ = (Real.sqrt (4 * H))⁻¹ / (8 * B) := by ring



theorem exists_uniform_birth_ball_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {H R : ℝ} (hH : 0 < H)
    (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H) (hR : 0 < R) :
    ∃ V : ℝ, 0 < V ∧ ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      SurgeryPrefixControls p F O → SurgeryFlowPinched F →
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
      ∀ origin ∈ surgeryObservationInterval O ∩ prefixFinalInterval p,
        ∀ q : (F.slice origin).carrier,
          (∀ y ∈ (F.metric origin).ball q (2 * R),
            (F.connection origin).scalarCurvature y ≤ 2 * H) →
          (∀ y ∈ connectedComponent q, ∀ v : TangentSpace (𝓡 3) y,
            0 ≤ (F.connection origin).ricci y v v) →
          (¬ SurgeryPositiveComponentAt F origin q ∨
            ∃ hT : origin ∈ F.surgery_times,
              ∀ [Nonempty (F.slice origin).carrier],
                ∃ i : Fin (F.event origin hT).cap_count,
                  (connectedComponent q ∩ ((F.event origin hT).caps i).carrier).Nonempty) →
          ENNReal.ofReal V ≤
            calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q (R / 2)) := by
  obtain ⟨d, r, hd, hr, hrR, htime, hmetric, hr1, hrepsilon, hrtime, hrcurv, hrscalar, hrtube⟩ :=
    exists_three_stop_scales S p hH (le_refl (M46.seedAnalyticConstant S)) hR
  obtain ⟨k, hk, hvolume⟩ := exists_three_stop_birth_volume P S p compatible hH hlevel
    (le_refl (M46.seedAnalyticConstant S)) hd hr htime hmetric hr1 hrepsilon
    hrtime hrcurv hrscalar hrtube
  refine ⟨k * (r / 2) ^ 3, by positivity, ?_⟩
  intro F O old hpinch hpolicy origin horigin q hscalar hRic hbirth
  have hsmall := hvolume F O old hpinch hpolicy origin horigin q
    (fun y hy => hscalar y (hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))) hRic hbirth
  apply hsmall.trans (measure_mono ?_)
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))

end PoincareConjecture.Proofs.M47
