import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ModelExponential
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_ExponentialFrameConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_GeodesicFields
import PoincareConjecture.Proofs.M44.Mathlib.ODEFirstVariation
import PoincareConjecture.Proofs.M44.Mathlib.UniformLinearEvaluation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

namespace NormalizedCapExponential

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta R : ℝ}
  {Q : SurgeryCapClose g₀ S g tip scale eta}



theorem phase_position_mem (D : NormalizedCapExponential Q R) {v : E} {t : ℝ}
    (ht : t • v ∈ ball 0 R) : (D.phase (v, t)).1 ∈ g₀.metric.ball 0 eta⁻¹ :=
  Q.toPartialDiffeomorph.map_target (D.map_mem _ ht)




theorem field_contDiffAt_phase (D : NormalizedCapExponential Q R) {v : E} {t : ℝ}
    (ht : t • v ∈ ball 0 R) :
    ContDiffAt ℝ ∞ (coordinateGeodesicField Q.normalizedCoefficients) (D.phase (v, t)) := by
  have hx := D.phase_position_mem ht
  exact contDiffAt_coordinateGeodesicField
    (Q.contDiffOn_normalizedCoefficients.contDiffAt
      (Q.toPartialDiffeomorph.open_source.mem_nhds hx))
    (Q.normalizedCoefficients_isInvertible hx)




theorem firstVariation_initial (D : NormalizedCapExponential Q R) (p v : E) :
    firstVariation D.phase (p, v) 0 =
      ((0, fderiv ℝ D.coordinateMap 0 p), (0, fderiv ℝ D.coordinateMap 0 v)) := by
  let L := fderiv ℝ D.coordinateMap 0
  have heq : (fun q => D.phase (q, 0)) = fun q => (0, L q) :=
    funext D.phase_initial
  have hd : HasFDerivAt (fun q => D.phase (q, 0)) ((0 : E →L[ℝ] E).prod L) p := by
    rw [heq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : E) p).prodMk L.hasFDerivAt
  rw [firstVariation, hd.fderiv, D.phase_initial]
  rfl

end NormalizedCapExponential



theorem standardFramePhase_firstVariation_initial
    (g₀ : StandardInitialMetric) (L : E ≃L[ℝ] E) (p v : E) :
    firstVariation (standardFramePhase g₀ L) (p, v) 0 = ((0, L p), (0, L v)) := by
  have heq : (fun q => standardFramePhase g₀ L (q, 0)) = fun q => (0, L q) :=
    funext (standardFramePhase_initial g₀ L)
  have hd : HasFDerivAt (fun q => standardFramePhase g₀ L (q, 0))
      ((0 : E →L[ℝ] E).prod L.toContinuousLinearMap) p := by
    rw [heq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : E) p).prodMk L.hasFDerivAt
  rw [firstVariation, hd.fderiv, standardFramePhase_initial]
  rfl

private theorem smul_mem_ball_of_half_radius {R : ℝ} {p : E} {t : ℝ}
    (hp : p ∈ ball 0 (R / 2)) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    t • p ∈ ball 0 R := by
  have hpR : ‖p‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hp
  have htR : |t| < 2 := abs_lt.mpr ht
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
  calc
    |t| * ‖p‖ ≤ 2 * ‖p‖ := mul_le_mul_of_nonneg_right htR.le (norm_nonneg p)
    _ < 2 * (R / 2) := mul_lt_mul_of_pos_left hpR (by norm_num)
    _ = R := by ring

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ) {R : ℝ}
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) R)




theorem tendstoUniformlyOn_initial_exponential_variations
    (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) {K V : Set E} (hK : IsCompact K) (hV : IsCompact V) :
    TendstoUniformlyOn (fun n z => firstVariation (D n).phase z 0)
      (fun z => firstVariation (standardFramePhase g₀ L) z 0) atTop (K ×ˢ V) := by
  have hp := ((hL.tendstoUniformlyOn_clm_apply hK).comp Prod.fst).mono
    (fun _ hz => hz.1 : K ×ˢ V ⊆ Prod.fst ⁻¹' K)
  have hv := ((hL.tendstoUniformlyOn_clm_apply hV).comp Prod.snd).mono
    (fun _ hz => hz.2 : K ×ˢ V ⊆ Prod.snd ⁻¹' V)
  have hzero : TendstoUniformlyOn (fun _ : ℕ => fun _ : E × E => (0 : E))
      (fun _ => 0) atTop (K ×ˢ V) := tendsto_const_nhds.tendstoUniformlyOn_const _
  have hboth := (hzero.prodMk_same hp).prodMk_same (hzero.prodMk_same hv)
  rw [Metric.tendstoUniformlyOn_iff] at hboth ⊢
  intro epsilon hepsilon
  filter_upwards [hboth epsilon hepsilon] with n hn
  intro z hz
  rw [(D n).firstVariation_initial z.1 z.2,
    standardFramePhase_firstVariation_initial g₀ L z.1 z.2]
  exact hn z hz





theorem tendstoUniformlyOn_exponential_firstVariations
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) {K V : Set E} (hK : IsCompact K) (hV : IsCompact V)
    (hKR : K ⊆ ball 0 (R / 2)) :
    TendstoUniformlyOn (fun n (z : (E × E) × ℝ) => firstVariation (D n).phase z.1 z.2)
      (fun z => firstVariation (standardFramePhase g₀ L) z.1 z.2)
      atTop ((K ×ˢ V) ×ˢ Icc (0 : ℝ) 1) := by
  have hR : 0 < R := (D 0).radius_pos
  have hsmall : ball (0 : E) (R / 2) ⊆ ball 0 R :=
    ball_subset_ball (by linarith)
  have hmodel : ContDiff ℝ ∞ (coordinateGeodesicField g₀.metric.euclideanCoefficients) :=
    contDiff_iff_contDiffAt.mpr fun z =>
      contDiffAt_coordinateGeodesicField (g₀.metric.contDiffAt_euclideanCoefficients z.1)
        (g₀.metric.inner_isInvertible z.1)
  apply tendstoUniformlyOn_firstVariation_of_compact_model
    (U := ball 0 (R / 2)) (I := Ioo (-2 : ℝ) 2) isOpen_ball isOpen_Ioo zero_le_one
    (by intro t ht; constructor <;> linarith [ht.1, ht.2]) hK hV hKR hmodel
    (standardFramePhase_contDiff g₀ L).contDiffOn
  · exact Eventually.of_forall fun n => (D n).phase_smooth.mono
      (fun _ hz => smul_mem_ball_of_half_radius hz.1 hz.2)
  · exact Eventually.of_forall fun n p hp t ht =>
      (D n).phase_hasDerivAt (hsmall hp) (smul_mem_ball_of_half_radius hp ht)
  · exact Eventually.of_forall fun n p hp t ht =>
      ((D n).field_contDiffAt_phase (smul_mem_ball_of_half_radius hp ht)).differentiableAt
        (by simp)
  · exact fun p _ t _ => standardFramePhase_hasDerivAt g₀ L p t
  · intro r
    rw [show (0 : E × E) = (0, 0) from rfl, ← closedBall_prod_same]
    exact tendstoUniformlyOn_initial_geodesicFields g₀ S g tip scale eta Q heta
      (isCompact_closedBall _ _) (isCompact_closedBall _ _)
  · intro r
    rw [show (0 : E × E) = (0, 0) from rfl, ← closedBall_prod_same]
    exact tendstoUniformlyOn_initial_fderiv_geodesicFields g₀ S g tip scale eta Q heta
      (isCompact_closedBall _ _) (isCompact_closedBall _ _)
  · exact tendstoUniformlyOn_initial_exponential_variations g₀ S g tip scale eta Q D L hL hK hV

end PoincareConjecture.M44
