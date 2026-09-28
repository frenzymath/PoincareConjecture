import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialHigherVariation
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_ExactBallCharts
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_IntrinsicJetConvergence
import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothPullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance adjustedMetricBilinearNormedGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance adjustedMetricBilinearNormedSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

namespace NormalizedCapExponential

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta R : ℝ}
  {Q : SurgeryCapClose g₀ S g tip scale eta}



noncomputable def adjustment (D : NormalizedCapExponential Q R) (L : E ≃L[ℝ] E) : E → E :=
  D.coordinateMap ∘ standardFrameLogarithm g₀ L




noncomputable def adjustedCoefficients (D : NormalizedCapExponential Q R)
    (L : E ≃L[ℝ] E) : E → Bilin :=
  fun x => scale⁻¹ ^ 2 • g.pullbackCoefficients (D.map ∘ standardFrameLogarithm g₀ L) x




theorem adjustedCoefficients_eq (D : NormalizedCapExponential Q R) (L : E ≃L[ℝ] E)
    {x : E} (hx : standardFrameLogarithm g₀ L x ∈ ball 0 R) :
    D.adjustedCoefficients L x =
      (Q.normalizedCoefficients (D.adjustment L x)).bilinearComp
        (fderiv ℝ (D.adjustment L) x) (fderiv ℝ (D.adjustment L) x) := by
  have ha : ContDiffAt ℝ ∞ (D.adjustment L) x :=
    (D.coordinateMap_smooth.contDiffAt (isOpen_ball.mem_nhds hx)).comp x
      (standardFrameLogarithm_contDiff g₀ L).contDiffAt
  have hsource : D.adjustment L x ∈ g₀.metric.ball 0 eta⁻¹ :=
    Q.toPartialDiffeomorph.map_target (D.map_mem _ hx)
  have he : MDifferentiableAt (𝓡 3) (𝓡 3) Q.map (D.adjustment L x) :=
    (Q.map_smooth.contMDiffAt
      (Q.toPartialDiffeomorph.open_source.mem_nhds hsource)).mdifferentiableAt (by simp)
  have hcomp : Q.map ∘ D.adjustment L =ᶠ[𝓝 x] D.map ∘ standardFrameLogarithm g₀ L := by
    have hlog := (standardFrameLogarithm_contDiff g₀ L).continuous.continuousAt (x := x)
    filter_upwards [hlog.preimage_mem_nhds (isOpen_ball.mem_nhds hx)] with y hy
    exact Q.right_inverse (D.map_mem _ hy)
  ext v w
  change scale⁻¹ ^ 2 * g.pullbackCoefficients
      (D.map ∘ standardFrameLogarithm g₀ L) x v w =
    scale⁻¹ ^ 2 * g.pullbackCoefficients Q.map (D.adjustment L x)
      (fderiv ℝ (D.adjustment L) x v) (fderiv ℝ (D.adjustment L) x w)
  rw [g.pullbackCoefficients_eq_of_comp_germ he (ha.differentiableAt (by simp)) hcomp]

end NormalizedCapExponential

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ) {R : ℝ}
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) R)




theorem compactSmoothConvergenceOn_initial_adjustments
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap))
    (hLinner : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w) :
    CompactSmoothConvergenceOn (fun n => (D n).adjustment L) id atTop
      (g₀.metric.ball 0 (R / 2)) := by
  have hR : 0 < R / 2 := half_pos (D 0).radius_pos
  have hU : IsOpen (g₀.metric.ball 0 (R / 2)) := by
    rw [M36.standard_ball_eq_euclidean g₀ hR]
    exact isOpen_ball
  have hlog : CompactSmoothConvergenceOn (fun _ : ℕ => standardFrameLogarithm g₀ L)
      (standardFrameLogarithm g₀ L) atTop (g₀.metric.ball 0 (R / 2)) :=
    CompactSmoothConvergenceOn.constant hU (standardFrameLogarithm_contDiff g₀ L).contDiffOn
  have hconv := (compactSmoothConvergenceOn_initial_exponentials
    g₀ S g tip scale eta Q D heta L hL).comp hlog
      (fun x hx => (standardFrameLogarithm_mem_ball g₀ L hLinner hR x).mpr hx)
  have heq : standardFrameExponential g₀ L ∘ standardFrameLogarithm g₀ L = id :=
    funext (standardFrameExponential_logarithm g₀ L)
  simpa only [heq, NormalizedCapExponential.adjustment] using hconv




theorem compactSmoothConvergenceOn_adjusted_metrics
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap))
    (hLinner : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w) :
    CompactSmoothConvergenceOn (fun n => (D n).adjustedCoefficients L)
      g₀.metric.euclideanCoefficients atTop (g₀.metric.ball 0 (R / 2)) := by
  have hB := compactSmoothConvergenceOn_initial_coefficients g₀ S g tip scale eta Q heta
  have ha := compactSmoothConvergenceOn_initial_adjustments g₀ S g tip scale eta Q D
    heta L hL hLinner
  have hpull := hB.pullback_bilinear ha (fun _ _ => mem_univ _)
  apply hpull.congr
  · intro n x hx
    apply (D n).adjustedCoefficients_eq L
    exact (ball_subset_ball (by linarith [(D 0).radius_pos]))
      ((standardFrameLogarithm_mem_ball g₀ L hLinner (half_pos (D 0).radius_pos) x).mpr hx)
  · intro x _
    ext v w
    simp only [id_eq, fderiv_id, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.id_apply]




theorem eventually_adjusted_intrinsic_jet_error_bound
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap))
    (hLinner : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w)
    {A : ℝ} (hA : 0 < A) (hAR : A < R / 2) (m : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ bound : ℝ, bound < epsilon ∧ ∀ᶠ n in atTop, ∀ x ∈ g₀.metric.ball 0 A,
      singularMetricJetErrorSquared g₀.metric g₀.connection
        (fun y v => (D n).adjustedCoefficients L y (v 0) (v 1)) m x ≤ bound := by
  have hK : IsCompact (closure (g₀.metric.ball 0 A)) := by
    rw [M36.standard_closure_ball g₀ hA]
    exact M36.standard_closed_ball_compact g₀ hA.le
  have hKU : closure (g₀.metric.ball 0 A) ⊆ g₀.metric.ball 0 (R / 2) := by
    rw [M36.standard_closure_ball g₀ hA]
    intro x hx
    exact hx.trans_lt (ENNReal.ofReal_lt_ofReal_iff (half_pos (D 0).radius_pos) |>.mpr hAR)
  obtain ⟨bound, hb, he⟩ := eventually_intrinsic_jet_error_bound g₀.metric g₀.connection
    (compactSmoothConvergenceOn_adjusted_metrics g₀ S g tip scale eta Q D heta L hL hLinner)
    hK hKU m hepsilon
  exact ⟨bound, hb, he.mono fun n hn x hx => hn x (subset_closure hx)⟩

end PoincareConjecture.M44
