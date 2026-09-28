import PoincareConjecture.Proofs.M47.CanonicalStandardTipCaps
import PoincareConjecture.Proofs.M47.CanonicalStandardMetricBounds
import PoincareConjecture.Proofs.M47.CanonicalStandardRecut
import PoincareConjecture.Proofs.M35.RawFlow.Completeness











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47




theorem standard_metric_complete {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {s : ℝ}
    (hs : s ∈ Ico 0 standard.flow.base.lifetime) :
    MetricComplete (standard.flow.metric s) := by
  have hsOne : s < 1 := by simpa only [standard.lifetime_one] using hs.2
  obtain ⟨K, _hK, hcompare⟩ := exists_standard_slab_metric_bound standard hs.1 hsOne
  apply RiemannianMetric.metricComplete_of_tangentNorm_le
    g0.metric (standard.flow.metric s) g0.complete
    (Real.exp_pos (K * |(0 : ℝ) - s|))
  intro x w
  have h := hcompare s ⟨hs.1, le_rfl⟩ 0 ⟨le_rfl, hs.1⟩ x w
  have hinitial : standard.flow.metric 0 = g0.metric := standard.flow.base.initial_metric
  rwa [hinitial] at h




theorem standard_tip_locus_setup_cap (S : RepairedControlledSchedulesData.{u})
    {s : ℝ} (hs : s ∈ Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime)
    {x : StandardCapSpace}
    (hdistance : ((S.cap_persistence.standard_cap.flow.metric s).edist 0 x).toReal *
      Real.sqrt ((S.cap_persistence.standard_cap.flow.connection s).scalarCurvature x) ≤
        (57 / 10 : ℝ) * S.setup.epsilon⁻¹) :
    ∃ H : CapCertificate (S.cap_persistence.standard_cap.flow.metric s),
      H.epsilon = S.setup.epsilon ∧ H.cap_constant ≤ S.setup.C ∧
      H.connection = S.cap_persistence.standard_cap.flow.connection s ∧ x ∈ H.core := by
  have hsOne : s < 1 := by
    simpa only [S.cap_persistence.standard_cap.lifetime_one] using hs.2
  obtain ⟨N, hNe, hNC, hND, hx⟩ :=
    standard_tip_locus_cap S hsOne ⟨hs.1, le_rfl⟩ hdistance
  have he := S.setup.epsilon_pos
  have hsmall : S.setup.epsilon ≤ 1 / 200 :=
    S.setup.epsilon_le.trans (min_le_left _ _)
  have hbeta := S.calibration.beta_lt_half
  have hgamma : N.epsilon ≤ 1 / 1200 := by
    rw [hNe]
    have h := mul_le_mul hbeta.le hsmall he.le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [h]
  have haccuracy : 6 * N.epsilon ≤ S.setup.epsilon := by
    rw [hNe]
    have h := mul_le_mul_of_nonneg_right hbeta.le he.le
    nlinarith only [h]
  obtain ⟨H, hHe, hHC, _hcarrier, hHD, hcore⟩ :=
    exists_same_constant_epsilon_recut N
      (standard_metric_complete S.cap_persistence.standard_cap hs)
      hgamma he hsmall haccuracy
  refine ⟨H, hHe, ?_, hHD.trans hND, hcore hx⟩
  rw [hHC, S.calibration.setup_C_eq]
  exact hNC.trans (le_max_right _ _)

end PoincareConjecture.Proofs.M47
