import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

theorem old_prefix_realized_ball_volume (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    {window : M33RegularHistoryWindow F} (R : M46RegularSpacetimeData window)
    {t r : ℝ} (ht : t ∈ R.history.generalized.interval)
    (htold : t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i)
    (y : (R.history.generalized.slice t).carrier)
    (hpositive : ¬ SurgeryPositiveComponentAt F t (R.history.history.forward t ht y))
    (hr : 0 < r) (hrle : r ≤ F.parameters.epsilon)
    (e : SurgeryFlowCylinder F (F.slice t) t 1 (Icc (-r ^ 2) 0)
      ((F.metric t).ball (R.history.history.forward t ht y) r))
    (hbase : ∀ h z,
      z ∈ (F.metric t).ball (R.history.history.forward t ht y) r →
        HEq (e.forward 0 h z) z)
    (hcurv : ∀ s hs z,
      z ∈ (F.metric t).ball (R.history.history.forward t ht y) r →
        (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs z) ≤ r⁻¹ ^ 2)
    (hregular : (F.metric t).ball (R.history.history.forward t ht y) r ⊆
      m33RegularRegion F t) :
    ENNReal.ofReal (p.kappa (Fin.last p.i) * r ^ 3) ≤
      calibratedMetricVolume (R.geometry.toLGeometry.slices t).metricOnPoints
        ((R.geometry.toLGeometry.slices t).metricOnPoints.ball
          ((R.geometry.sliceIdentification t).identification y) r) := by
  have hvolume := old.noncollapsed (Fin.last p.i) (by simp) t htold
    (O.interval_subset htold.1) (R.history.history.forward t ht y)
    hpositive r hr hrle e hbase hcurv
  change ENNReal.ofReal (p.kappa (Fin.last p.i) * r ^ 3) ≤
    calibratedMetricVolume (R.geometry.realization.slices t).metricOnPoints
      ((R.geometry.realization.slices t).metricOnPoints.ball
        ((R.geometry.sliceIdentification t).identification y) r)
  rw [← M13.originalSlice_ball R.geometry P.m13 t y r,
    M13.originalSlice_volume R.geometry P.m13 t,
    R.history.ball_volume_of_subset t ht y r hregular]
  exact hvolume

theorem HalfRadiusHistory.old_prefix_ball_volume (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D)
    (hancestry : PositiveAncestorExclusion H)
    {tau r : ℝ} (htau : 0 < tau)
    (ht : D.time - tau ∈ H.spacetime.history.generalized.interval)
    (htold : D.time - tau ∈ surgeryObservationInterval O ∩ surgeryEpochEntry p.i)
    (y : (H.spacetime.history.generalized.slice (D.time - tau)).carrier)
    (hpath : Nonempty (M14BackwardPath H.spacetime.geometry.toLGeometry D.time 0 tau
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
      ((H.spacetime.geometry.sliceIdentification (D.time - tau)).identification y).val))
    (hr : 0 < r) (hrle : r ≤ F.parameters.epsilon)
    (e : SurgeryFlowCylinder F (F.slice (D.time - tau)) (D.time - tau) 1
      (Icc (-r ^ 2) 0)
      ((F.metric (D.time - tau)).ball
        (H.spacetime.history.history.forward (D.time - tau) ht y) r))
    (hbase : ∀ h z,
      z ∈ (F.metric (D.time - tau)).ball
        (H.spacetime.history.history.forward (D.time - tau) ht y) r →
      HEq (e.forward 0 h z) z)
    (hcurv : ∀ s hs z,
      z ∈ (F.metric (D.time - tau)).ball
        (H.spacetime.history.history.forward (D.time - tau) ht y) r →
      (F.connection (D.time - tau + s / 1)).curvatureTensorNorm
        (e.forward s hs z) ≤ r⁻¹ ^ 2)
    (hregular : (F.metric (D.time - tau)).ball
      (H.spacetime.history.history.forward (D.time - tau) ht y) r ⊆
        m33RegularRegion F (D.time - tau)) :
    ENNReal.ofReal (p.kappa (Fin.last p.i) * r ^ 3) ≤ calibratedMetricVolume
      (H.spacetime.geometry.toLGeometry.slices (D.time - tau)).metricOnPoints
      ((H.spacetime.geometry.toLGeometry.slices (D.time - tau)).metricOnPoints.ball
        ((H.spacetime.geometry.sliceIdentification (D.time - tau)).identification y) r) :=
  old_prefix_realized_ball_volume P p old H.spacetime ht htold y
    (hancestry tau htau ht y hpath) hr hrle e hbase hcurv hregular

end PoincareConjecture.Proofs.M46
