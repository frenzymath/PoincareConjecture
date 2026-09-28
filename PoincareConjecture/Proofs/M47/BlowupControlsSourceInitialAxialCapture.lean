import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialAxialDistance
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialLocalDistance
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoining

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

private theorem initial_comparison_radius_buffer
    {g0 : StandardInitialMetric} {A eta r : ℝ}
    (heta : 0 < eta) (hr : 0 < r) (hA : r + 2 < A)
    (hballs : g0.metric.ball 0 A ⊆ g0.metric.ball 0 (eta⁻¹ + 1)) :
    r < eta⁻¹ ∧ eta < 1 := by
  have hrad : 0 < r + 2 := by linarith
  obtain ⟨z, hz⟩ := exists_norm_eq StandardCapSpace
    ((M36.radialEuclideanRadius_pos_iff g0 (r + 2)).mpr hrad).le
  have heq : g0.metric.edist 0 z = ENNReal.ofReal (r + 2) := by
    rw [M36.standard_edist_zero, hz, M36.radialArclength_euclideanRadius]
  have hin : z ∈ g0.metric.ball 0 A := by
    change g0.metric.edist 0 z < _
    rw [heq]
    exact (ENNReal.ofReal_lt_ofReal_iff (hrad.trans hA)).mpr hA
  have hout := hballs hin
  change g0.metric.edist 0 z < ENNReal.ofReal (eta⁻¹ + 1) at hout
  rw [heq] at hout
  have hrange : r + 2 < eta⁻¹ + 1 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < eta⁻¹ + 1)).mp hout
  have hinv : 1 < eta⁻¹ := by linarith
  refine ⟨by linarith, ?_⟩
  have h := mul_lt_mul_of_pos_left hinv heta
  simpa only [mul_one, mul_inv_cancel₀ heta.ne'] using h

theorem source_initial_old_map_height_lt
    {F : SurgeryFlowData.{u}} {t : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {A r : ℝ} (initial : SurgeryCapInitialComparison F t hT i A)
    (hr : 0 < r) (hA : r + 2 < A)
    {x : StandardCapSpace} (hx : x ∈ F.standard_initial.metric.ball 0 r)
    (havoid : initial.chart x ∉ ((F.event t hT).caps i).carrier) :
    |(((F.event t hT).necks i).neck.coordinate_inverse
      (sourceInitialOldMap initial x)).2| < 4 * r := by
  let E := F.event t hT
  let N := (E.necks i).neck
  let R := E.local_result i
  let y := sourceInitialOldMap initial x
  have hxA : x ∈ F.standard_initial.metric.ball 0 A :=
    hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith only [hA]))
  have hret := source_initial_chart_retention hT i initial hxA havoid
  have hy : y ∈ N.region (-N.epsilon⁻¹) 0 := hret.2.2
  obtain ⟨eta, heta, Q, _hdelta, hballs, hlink⟩ := initial.local_metric_link
  obtain ⟨hrEta, hetaOne⟩ := initial_comparison_radius_buffer heta hr hA hballs
  have hQdistance := source_initial_comparison_tip_distance_lt Q hetaOne.le hrEta.le hx
  have hpre : E.retention.inverse (initial.chart x) ∈ E.regular_limit :=
    E.retained_pre_subset (interior_subset hret.2.1)
  have hlimit : E.limit_identify.inverse y = E.retention.inverse (initial.chart x) :=
    E.limit_identify.left_inverse hpre
  have hpoint : E.retention.map (E.limit_identify.inverse y) = initial.chart x := by
    rw [hlimit]
    exact E.retention.right_inverse (interior_subset hret.1)
  have hQpoint : Q.map x = R.collapse y := by
    apply E.local_embed_injective i
    calc
      E.local_embed i (Q.map x) = initial.chart x := (hlink x hxA).symm
      _ = E.retention.map (E.limit_identify.inverse y) := hpoint.symm
      _ = E.local_embed i (R.collapse y) := (E.local_retention i y hy).symm
  rw [hQpoint] at hQdistance
  have hheight := (source_initial_old_height_le_tip_distance R hy).trans_lt hQdistance
  have hreal : N.scale / 2 * |(N.coordinate_inverse y).2| < 2 * N.scale * r :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos (mul_pos (by norm_num) N.scale_pos) hr)).mp hheight
  change |(N.coordinate_inverse y).2| < 4 * r
  nlinarith only [hreal, N.scale_pos]

end PoincareConjecture.M47
