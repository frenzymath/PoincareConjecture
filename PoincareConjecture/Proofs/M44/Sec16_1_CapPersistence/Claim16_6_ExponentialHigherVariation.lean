import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialVariation
import PoincareConjecture.Proofs.M44.Mathlib.ODEHigherVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ) {R : ℝ}
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) R)

theorem compactSmoothConvergenceOn_initial_exponential_phases
    (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) :
    CompactSmoothConvergenceOn (fun n p => (D n).phase (p, 0))
      (fun p => standardFramePhase g₀ L (p, 0)) atTop univ := by
  have hz : CompactSmoothConvergenceOn (fun _ : ℕ => fun _ : E => (0 : E))
      (fun _ => 0) atTop univ :=
    CompactSmoothConvergenceOn.constant isOpen_univ contDiffOn_const
  simpa only [NormalizedCapExponential.phase_initial, standardFramePhase_initial,
    ContinuousLinearEquiv.coe_coe] using
    hz.prodMk hL.compactSmoothConvergenceOn_clm_apply

theorem tendstoUniformlyOn_exponential_phase_jets
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) (j : ℕ) {K : Set E} (hK : IsCompact K)
    (hKR : K ⊆ ball 0 (R / 2)) :
    TendstoUniformlyOn
      (fun n (z : E × ℝ) => iteratedFDeriv ℝ j (fun p => (D n).phase (p, z.2)) z.1)
      (fun z : E × ℝ => iteratedFDeriv ℝ j
        (fun p => standardFramePhase g₀ L (p, z.2)) z.1) atTop (K ×ˢ Icc (0 : ℝ) 1) := by
  have hR := (D 0).radius_pos
  have hsmall : ball (0 : E) (R / 2) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hsmul {p : E} {t : ℝ} (hp : p ∈ ball 0 (R / 2)) (ht : t ∈ Ioo (-2 : ℝ) 2) :
      t • p ∈ ball 0 R := by
    have hpR : ‖p‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hp
    have htR : |t| < 2 := abs_lt.mpr ht
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖p‖ ≤ 2 * ‖p‖ := mul_le_mul_of_nonneg_right htR.le (norm_nonneg p)
      _ < 2 * (R / 2) := mul_lt_mul_of_pos_left hpR (by norm_num)
      _ = R := by ring
  apply tendstoUniformlyOn_ode_spatial_jets j
    (U := ball 0 (R / 2)) (I := Ioo (-2 : ℝ) 2) isOpen_ball isOpen_Ioo zero_le_one
    (by intro t ht; constructor <;> linarith [ht.1, ht.2]) hK hKR
    (standardFramePhase_contDiff g₀ L).contDiffOn
  · exact Eventually.of_forall fun n => (D n).phase_smooth.mono (fun _ hz => hsmul hz.1 hz.2)
  · exact Eventually.of_forall fun n p hp t ht =>
      (D n).phase_hasDerivAt (hsmall hp) (hsmul hp ht)
  · exact Eventually.of_forall fun n p hp t ht => (D n).field_contDiffAt_phase (hsmul hp ht)
  · exact fun p _ t _ => standardFramePhase_hasDerivAt g₀ L p t
  · exact compactSmoothConvergenceOn_initial_geodesicFields g₀ S g tip scale eta Q heta
  · exact (compactSmoothConvergenceOn_initial_exponential_phases
      g₀ S g tip scale eta Q D L hL).mono isOpen_ball (subset_univ _)

theorem compactSmoothConvergenceOn_initial_exponentials
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap)) :
    CompactSmoothConvergenceOn (fun n => (D n).coordinateMap)
      (standardFrameExponential g₀ L) atTop (ball 0 (R / 2)) := by
  have hsmall : ball (0 : E) (R / 2) ⊆ ball 0 R :=
    ball_subset_ball (by linarith [(D 0).radius_pos])
  have hs (n : ℕ) : ContDiffOn ℝ ∞ (fun p => (D n).phase (p, 1)) (ball 0 (R / 2)) :=
    (D n).phase_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun p hp => by simpa only [mem_ofPred_eq, one_smul] using hsmall hp)
  have hphase : CompactSmoothConvergenceOn (fun n p => (D n).phase (p, 1))
      (fun p => standardFramePhase g₀ L (p, 1)) atTop (ball 0 (R / 2)) := {
    isOpen := isOpen_ball
    smooth := ((standardFramePhase_contDiff g₀ L).comp
      (contDiff_id.prodMk contDiff_const)).contDiffOn
    eventually_smooth K _ hK := Eventually.of_forall fun n x hx =>
      (hs n).contDiffAt (isOpen_ball.mem_nhds (hK hx))
    jets j K hK hKR := by
      have hjet := tendstoUniformlyOn_exponential_phase_jets
        g₀ S g tip scale eta Q D heta L hL j hK hKR
      exact (hjet.comp (fun p : E => (p, (1 : ℝ)))).mono (fun _ hp => ⟨hp, by simp⟩) }
  have hproj := hphase.comp_smooth isOpen_univ
    (contDiff_fst (𝕜 := ℝ) (n := ∞)).contDiffOn (fun _ _ => mem_univ _)
  simpa only [Function.comp_def, NormalizedCapExponential.phase, standardFramePhase, one_smul]
    using hproj

end PoincareConjecture.M44
