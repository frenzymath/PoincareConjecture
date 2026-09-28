import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MetricExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactExtension














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

open RiemannianMetric




theorem m64Intrinsic_euclidean_edist_le_of_uniform_lower
    (G : RiemannianMetric 2 AnnulusCoordinates) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ p v : AnnulusCoordinates, c * ‖v‖ ≤ G.tangentNorm p v)
    (x y : AnnulusCoordinates) :
    EDist.edist x y ≤ ENNReal.ofReal c⁻¹ * G.edist x y := by
  have hbound (p v : AnnulusCoordinates) :
      (euclideanMetric 2).tangentNorm p v ≤ c⁻¹ * G.tangentNorm p v := by
    rw [RiemannianMetric.euclideanMetric_tangentNorm]
    have h := mul_le_mul_of_nonneg_left (hlower p v) (inv_pos.mpr hc).le
    simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h
  let r := (G.edist x y).toReal + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  rw [← RiemannianMetric.euclideanMetric_edist]
  apply RiemannianMetric.edist_le_mul_edist_of_tangentNorm_le_on_ball G
    (euclideanMetric 2) x r c⁻¹ hr (inv_pos.mpr hc) (fun p _ v => hbound p v)
  · change G.edist x x < ENNReal.ofReal r
    have hself : G.edist x x = 0 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
        ⟨G.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr hr
  · change G.edist x y < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal (G.edist_ne_top x y)]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    dsimp only [r]
    linarith



theorem m64Intrinsic_isCompact_closure_ball_of_uniform_lower
    (G : RiemannianMetric 2 AnnulusCoordinates) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ p v : AnnulusCoordinates, c * ‖v‖ ≤ G.tangentNorm p v)
    (x : AnnulusCoordinates) {R : ℝ} (hR : 0 < R) :
    IsCompact (closure (G.ball x R)) := by
  have hsub : G.ball x R ⊆ Metric.closedBall x (c⁻¹ * R) := by
    intro y hy
    have hmul : ENNReal.ofReal c⁻¹ * G.edist x y ≤
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal R := by
      gcongr
      exact hy.le
    have hd := (m64Intrinsic_euclidean_edist_le_of_uniform_lower G hc hlower x y).trans
      hmul
    rw [edist_dist, ← ENNReal.ofReal_mul (inv_pos.mpr hc).le] at hd
    rw [Metric.mem_closedBall, dist_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_pos (inv_pos.mpr hc) hR).le).mp hd
  exact (isCompact_closedBall x (c⁻¹ * R)).of_isClosed_subset isClosed_closure
    (closure_minimal hsub Metric.isClosed_closedBall)




theorem m64Intrinsic_exists_extension_with_geodesic_initial_data (N : IntrinsicAnnulus) :
    ∃ G : RiemannianMetric 2 AnnulusCoordinates,
      (∀ p ∈ standardAnnulusDomain,
        G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients) ∧
      ∀ p v : AnnulusCoordinates, ∃ epsilon : ℝ, 0 < epsilon ∧
        ∃ gamma : ℝ → AnnulusCoordinates,
          G.IsGeodesicOn gamma (Ioo (-epsilon) (1 + epsilon)) ∧
          gamma 0 = p ∧ HasDerivAt gamma v 0 := by
  obtain ⟨G, c, hc, heq, hlower, _⟩ := m64Intrinsic_exists_uniformly_positive_extension N
  refine ⟨G, heq, ?_⟩
  intro p v
  let speed := Real.sqrt (G.pullbackCoefficients (extChartAt (𝓡 2) p).symm
    (extChartAt (𝓡 2) p p) v v)
  have hR : 0 < speed + 1 := by dsimp only [speed]; positivity
  obtain ⟨epsilon, hepsilon, gamma, hgeo, hzero, hderiv, _⟩ :=
    G.exists_geodesic_through_one_of_precompact_ball p hR
      (m64Intrinsic_isCompact_closure_ball_of_uniform_lower G hc hlower p hR)
      v (show speed < speed + 1 by linarith)
  refine ⟨epsilon, hepsilon, gamma, hgeo, hzero, ?_⟩
  simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using hderiv

end PoincareConjecture
