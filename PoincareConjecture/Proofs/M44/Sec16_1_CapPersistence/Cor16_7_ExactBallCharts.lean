import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_PhysicalExponentialBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

noncomputable def standardFrameDiffeomorph (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) :
    Diffeomorph (𝓡 3) (𝓡 3) E E ∞ where
  toFun := standardFrameExponential g₀ L
  invFun := standardFrameLogarithm g₀ L
  left_inv := standardFrameLogarithm_exponential g₀ L
  right_inv := standardFrameExponential_logarithm g₀ L
  contMDiff_toFun := (standardFrameExponential_contDiff g₀ L).contMDiff
  contMDiff_invFun := (standardFrameLogarithm_contDiff g₀ L).contMDiff

theorem standardFrameLogarithm_mem_ball
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E)
    (hL : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w)
    {r : ℝ} (hr : 0 < r) (x : E) :
    standardFrameLogarithm g₀ L x ∈ ball 0 r ↔ x ∈ g₀.metric.ball 0 r := by
  constructor
  · intro hx
    have h := mem_image_of_mem (standardFrameExponential g₀ L) hx
    rw [standardFrameExponential_image_ball g₀ L hL hr,
      standardFrameExponential_logarithm] at h
    exact h
  · intro hx
    have h := mem_image_of_mem (standardFrameLogarithm g₀ L) hx
    rw [standardFrameLogarithm_image_ball g₀ L hL hr] at h
    exact h

theorem isCompact_normalized_ball_of_small_tolerance
    {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta R : ℝ}
    (Q : SurgeryCapClose g₀ S g tip scale eta) (hR : 0 < R)
    (heta : eta ≤ min (1 / 2) (2 * R + 2)⁻¹) :
    IsCompact (closure (Q.normalizedMetric.ball tip R)) := by
  have hhalf : eta ≤ 1 / 2 := heta.trans (min_le_left _ _)
  have hinv := one_div_le_one_div_of_le Q.eta_pos (heta.trans (min_le_right _ _))
  simp only [one_div, inv_inv] at hinv
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - eta) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hbound : R ≤ Real.sqrt (1 - eta) * (2 * R + 1) := calc
    R ≤ (1 / 2) * (2 * R + 1) := by linarith
    _ ≤ Real.sqrt (1 - eta) * (2 * R + 1) :=
      mul_le_mul_of_nonneg_right hroot (by linarith)
  exact (Q.isCompact_closure_normalized_ball (by linarith)
    (r := 2 * R + 1) (by linarith) (by linarith)).of_isClosed_subset isClosed_closure
      (closure_mono (fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hbound)))

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ) {R : ℝ}
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) R)

theorem eventually_initial_exactBall_charts
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap))
    (hLinner : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w)
    {A : ℝ} (hA : 0 < A) (hAR : A < R / 2) :
    ∀ᶠ n in atTop, ∃ C : PartialDiffeomorph (𝓡 3) (𝓡 3) E (S n).carrier ∞,
      (C : E → (S n).carrier) = (D n).map ∘ standardFrameLogarithm g₀ L ∧
      C.source = g₀.metric.ball 0 A ∧ C.target = (Q n).normalizedMetric.ball (tip n) A ∧
      C 0 = tip n ∧ ∀ r : ℝ, 0 < r → r ≤ A →
        C '' g₀.metric.ball 0 r = (Q n).normalizedMetric.ball (tip n) r := by
  have hR : 0 < R := (D 0).radius_pos
  have hdelta : 0 < min (1 / 2 : ℝ) (2 * R + 2)⁻¹ :=
    lt_min (by norm_num) (inv_pos.mpr (by linarith))
  have hcompact : ∀ᶠ n in atTop, IsCompact (closure ((Q n).normalizedMetric.ball (tip n) R)) := by
    filter_upwards [heta.eventually (gt_mem_nhds hdelta)] with n hn
    exact isCompact_normalized_ball_of_small_tolerance (Q n) hR hn.le
  filter_upwards [hcompact,
    eventually_initial_exponential_charts g₀ S g tip scale eta Q D heta L hL hA hAR]
    with n hn hchart
  obtain ⟨e, he, hes, het⟩ := hchart
  let C := (standardFrameDiffeomorph g₀ L).symm.toPartialDiffeomorph.trans e
  have hmap : (C : E → (S n).carrier) = (D n).map ∘ standardFrameLogarithm g₀ L := by
    change (fun x => e (standardFrameLogarithm g₀ L x)) = _
    rw [he]
    rfl
  have hsource : C.source = g₀.metric.ball 0 A := by
    change univ ∩ standardFrameLogarithm g₀ L ⁻¹' e.source = _
    rw [hes, univ_inter]
    ext x
    exact standardFrameLogarithm_mem_ball g₀ L hLinner hA x
  have htarget : C.target = (Q n).normalizedMetric.ball (tip n) A := by
    change e.target ∩ e.symm ⁻¹' univ = _
    rw [preimage_univ, inter_univ, het, (D n).image_ball hn hA (by linarith)]
  refine ⟨C, hmap, hsource, htarget, ?_, ?_⟩
  · rw [hmap]
    change (D n).map (L.symm (standardRadialLogarithm g₀ 0)) = tip n
    rw [standardRadialLogarithm_zero, map_zero, (D n).map_zero]
  · intro r hr hrA
    calc
      C '' g₀.metric.ball 0 r =
          (D n).map '' (standardFrameLogarithm g₀ L '' g₀.metric.ball 0 r) := by
        rw [image_image, hmap]
        rfl
      _ = (Q n).normalizedMetric.ball (tip n) r := by
        rw [standardFrameLogarithm_image_ball g₀ L hLinner hr]
        exact (D n).image_ball hn hr (by linarith)

end PoincareConjecture.M44
