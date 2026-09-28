import PoincareConjecture.Proofs.M60.Mathlib.SUPlaneMeanValue
import PoincareConjecture.Proofs.M60.Mathlib.SUHeinzPointPicking










noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ContDiff

namespace PoincareConjecture.M60




theorem exists_positive_heinz_estimate :
    ∃ A : ℝ, 0 < A ∧ ∀ (K R : ℝ), 0 ≤ K → 0 < R → R ≤ 1 →
      ∀ u : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiff ℝ ∞ u → (∀ x, 0 < u x) →
        (∀ x ∈ Metric.ball 0 R, -K * (u x) ^ 2 ≤ suPlaneLaplacian u x) →
        A * K * (∫ x in Metric.closedBall 0 R, u x) ≤ 1 →
        R ^ 2 * u 0 ≤ A * (∫ x in Metric.closedBall 0 R, u x) := by
  obtain ⟨C, hC, hmean⟩ := exists_plane_mean_value_sq
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨32 * C ^ 2, by positivity, fun K R hK hR hR1 u hu hpos hlap hsmall => ?_⟩
  let E : ℝ := ∫ x in Metric.closedBall 0 R, u x
  obtain ⟨p, s, hs, hsR, hup, hsub, hcenter, hbound⟩ := exists_heinz_disk hR
    hu.continuous.continuousOn (fun x _ => (hpos x).le) (hpos 0)
  let B : ℝ := 1 + 4 * K * u p * s ^ 2
  have hB : 1 ≤ B := le_add_of_nonneg_right (by positivity)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hroot : 1 ≤ Real.sqrt B := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hB
  have hrootpos : 0 < Real.sqrt B := lt_of_lt_of_le zero_lt_one hroot
  let r : ℝ := s / Real.sqrt B
  have hr : 0 < r := div_pos hs hrootpos
  have hrs : r ≤ s := div_le_self hs.le hroot
  have hr1 : r ≤ 1 := by linarith
  have hrsq : r ^ 2 = s ^ 2 / B := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt hBpos.le]
  have hscale : 4 * K * u p ≤ 1 / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    rw [hrsq, ← mul_div_assoc]
    apply (div_le_iff₀ hBpos).mpr
    dsimp only [B]
    linarith
  have hball : Metric.closedBall p r ⊆ Metric.closedBall p s :=
    Metric.closedBall_subset_closedBall hrs
  have hlinear (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Metric.ball p r) :
      -(1 / r ^ 2) * u x ≤ suPlaneLaplacian u x := by
    have hxs := hball (Metric.ball_subset_closedBall hx)
    have hb := hbound x hxs
    have hm := mul_le_mul_of_nonneg_left hb hK
    have hc : K * u x ≤ 1 / r ^ 2 := by nlinarith only [hm, hscale]
    have ht := mul_le_mul_of_nonneg_right hc (hpos x).le
    have hl := hlap x (hsub hxs)
    nlinarith only [ht, hl]
  have hm := hmean u hu hpos p r hr hr1 hlinear
  have hhalf : Metric.closedBall p (r / 2) ⊆ Metric.closedBall p s :=
    Metric.closedBall_subset_closedBall (by linarith)
  have houter : Metric.closedBall p (r / 2) ⊆ Metric.closedBall 0 R :=
    hhalf.trans (hsub.trans Metric.ball_subset_closedBall)
  have hiu : IntegrableOn u (Metric.closedBall p (r / 2)) volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) hu.continuous.continuousOn
  have hiu2 : IntegrableOn (fun x => (u x) ^ 2) (Metric.closedBall p (r / 2)) volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
      (hu.continuous.pow 2).continuousOn
  have hie : IntegrableOn u (Metric.closedBall 0 R) volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) hu.continuous.continuousOn
  have hmass : (∫ x in Metric.closedBall p (r / 2), u x) ≤ E :=
    setIntegral_mono_set hie (Eventually.of_forall fun x => (hpos x).le)
      (Eventually.of_forall fun _ hx => houter hx)
  have henergy : (∫ x in Metric.closedBall p (r / 2), (u x) ^ 2) ≤ 4 * u p * E := by
    calc
      _ ≤ ∫ x in Metric.closedBall p (r / 2), (4 * u p) * u x := by
        apply integral_mono_ae hiu2 (hiu.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        have hb := mul_le_mul_of_nonneg_right (hbound x (hhalf hx)) (hpos x).le
        nlinarith only [hb]
      _ = (4 * u p) * (∫ x in Metric.closedBall p (r / 2), u x) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have hsquare := hm.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg C))
  have hpoint : r ^ 2 * u p ≤ 4 * C ^ 2 * E := by
    apply (mul_le_mul_iff_right₀ hup).mp
    nlinarith only [hsquare]
  have hT : s ^ 2 * u p ≤ (4 * C ^ 2 * E) * B := by
    apply (div_le_iff₀ hBpos).mp
    simpa only [hrsq, div_mul_eq_mul_div] using hpoint
  have hsmallT := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg (sq_nonneg s) hup.le)
  change (32 * C ^ 2 * K * E) * (s ^ 2 * u p) ≤ 1 * (s ^ 2 * u p) at hsmallT
  have hTbound : s ^ 2 * u p ≤ 8 * C ^ 2 * E := by
    dsimp only [B] at hT
    nlinarith only [hT, hsmallT]
  change R ^ 2 * u 0 ≤ 32 * C ^ 2 * E
  nlinarith only [hcenter, hTbound]

end PoincareConjecture.M60
