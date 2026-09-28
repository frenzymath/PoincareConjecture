import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialFrames
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialJetConvergence
import PoincareConjecture.Proofs.M44.Mathlib.FrameCompactness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance exponentialFrameBilinNormedAddCommGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance exponentialFrameBilinNormedSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta R : ℕ → ℝ)
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) (R n))



theorem exists_initial_exponential_frame_bound (heta : Tendsto eta atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ‖fderiv ℝ (D n).coordinateMap 0‖ ≤ C := by
  obtain ⟨c, hc, hbound⟩ := SurgeryCapClose.exists_normalized_uniform_lower_bound
    g₀ (isCompact_singleton (x := (0 : E)))
  obtain ⟨delta, hdelta, hdomain⟩ := exists_initial_comparison_domain_threshold
    g₀ (isCompact_singleton (x := (0 : E))) 0
  refine ⟨Real.sqrt c⁻¹, Real.sqrt_pos.mpr (inv_pos.mpr hc), ?_⟩
  filter_upwards [heta.eventually (gt_mem_nhds (lt_min (by norm_num : (0 : ℝ) < 1 / 2)
    hdelta))] with n hn
  apply norm_frame_le_of_quadratic_lower_bound hc
    (fun v => hbound (S n) (g n) (tip n) (scale n) (eta n) (Q n)
      (hn.le.trans (min_le_left _ _))
      ((hdomain (eta n) (Q n).eta_pos (hn.le.trans (min_le_right _ _))).2)
      0 (mem_singleton 0) v)
    (fderiv ℝ (D n).coordinateMap 0) (D n).coordinate_frame_inner




theorem exists_subseq_initial_exponential_frames (heta : Tendsto eta atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ L₀ : E ≃L[ℝ] E,
      Tendsto (fun n => fderiv ℝ (D (φ n)).coordinateMap 0) atTop
        (𝓝 L₀.toContinuousLinearMap) ∧
      ∀ v w, g₀.metric.inner 0 (L₀ v) (L₀ w) = inner ℝ v w := by
  have hzero : TendstoUniformlyOn (fun n => (Q n).normalizedCoefficients)
      g₀.metric.euclideanCoefficients atTop ({0} : Set E) := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → E)).comp_tendstoUniformlyOn
        (tendstoUniformlyOn_initial_coefficient_jets g₀ S g tip scale eta Q heta 0
          (isCompact_singleton (x := (0 : E))))
  obtain ⟨C, _, hC⟩ := exists_initial_exponential_frame_bound g₀ S g tip scale eta R Q D heta
  exact exists_subseq_orthonormal_frame_of_eventual_bound (hzero.tendsto_at (mem_singleton 0))
    (fun n => fderiv ℝ (D n).coordinateMap 0) (fun n => (D n).coordinate_frame_inner) hC

end PoincareConjecture.M44
