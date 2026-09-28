import PoincareConjecture.Proofs.M46.RegularSpacetime
import PoincareConjecture.Proofs.M15.RawBallCylinder
import PoincareConjecture.Proofs.M33.HistoryMetric











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture

theorem M46Predecessors.uniformConfigurationData (P : M46Predecessors.{u})
    (taubar l0 V : ℝ) (ht : 0 < taubar) (hl : 0 < l0) (hV : 0 < V) :
    Nonempty (M15GeneralizedUniformData.{u} 3 taubar l0 V) :=
  P.m15.uniform taubar l0 V ht hl hV

variable {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
  (P : M46Predecessors.{u}) {F : SurgeryFlowData.{u}}
  {W : M33RegularHistoryWindow F} (R : M46RegularSpacetimeData W)
  {T r : ℝ} (ht : T ∈ R.history.generalized.interval)
  (x : (R.history.generalized.slice T).carrier) (hr : 0 < r)
  (e : GeneralizedFlowCylinder R.history.generalized (R.history.generalized.slice T)
    T 1 (Icc (-r ^ 2) 0) ((R.history.generalized.metric T).ball x r))
  (hI : Icc (T - r ^ 2) T ⊆ R.history.generalized.interval)
  (hbase : ∀ h y, y ∈ (R.history.generalized.metric T).ball x r →
    e.pointMap 0 h y = (⟨T, y⟩ : R.history.generalized.point))
  (hcurv : ∀ s hs y, y ∈ (R.history.generalized.metric T).ball x r →
    R.history.generalized.curvatureNorm (e.pointMap s hs y) ≤ r⁻¹ ^ 2)
  (E : M14ExponentialFamily R.geometry.toLGeometry T
    ((R.geometry.sliceIdentification T).identification x).val)
  (Q : M15Theorem81Configuration R.geometry.toLGeometry T
    ((R.geometry.sliceIdentification T).identification x) E taubar l0 V r _ _
    (Proofs.M15.rawActualBallCylinder R.geometry P.m13 x hr e hI hbase hcurv))

include Q

theorem M46RegularSpacetimeData.configuration_volume :
    ENNReal.ofReal (U.kappa * r ^ 3) ≤ calibratedMetricVolume (F.metric T)
      ((F.metric T).ball (R.history.history.forward T ht x) r) := by
  have h := U.estimate _ _ _ R.geometry.toLGeometry T
    ((R.geometry.sliceIdentification T).identification x) E r _
    (Proofs.M15.rawBallSource R.history.generalized T x r)
    (Proofs.M15.rawActualBallCylinder R.geometry P.m13 x hr e hI hbase hcurv) Q
  change ENNReal.ofReal (U.kappa * r ^ 3) ≤
    calibratedMetricVolume (R.geometry.realization.slices T).metricOnPoints
      ((R.geometry.realization.slices T).metricOnPoints.ball
        ((R.geometry.sliceIdentification T).identification x) r) at h
  rw [← Proofs.M13.originalSlice_ball R.geometry P.m13 T x r,
    Proofs.M13.originalSlice_volume R.geometry P.m13 T
      ((R.history.generalized.metric T).ball x r), ← R.history.volume_image T ht] at h
  exact h.trans (measure_mono (R.history.history.ball_image_subset T ht x r))

theorem M46RegularSpacetimeData.configuration_half_radius {rho : ℝ}
    (hhalf : r = rho / 2) :
    ENNReal.ofReal ((U.kappa / 8) * rho ^ 3) ≤ calibratedMetricVolume (F.metric T)
      ((F.metric T).ball (R.history.history.forward T ht x) rho) := by
  have h := R.configuration_volume U P ht x hr e hI hbase hcurv E Q
  have heq : (U.kappa / 8) * rho ^ 3 = U.kappa * r ^ 3 := by rw [hhalf]; ring
  rw [heq]
  apply h.trans (measure_mono ?_)
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith [hr]))

end PoincareConjecture
