import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Inclusions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.StandardBalls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem isCompact_closed_cap :
    IsCompact (closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))) := by
  rw [← R.cap_closed_image]
  apply (MetricSurgery.standard_closed_ball_compact g₀
    (by linarith [g₀.cylindrical_end.radius_pos])).image_of_continuousOn
  apply R.cap_map_smooth.continuousOn.mono
  intro x hx
  exact lt_of_le_of_lt hx (ENNReal.ofReal_lt_ofReal_iff
    (by linarith [g₀.cylindrical_end.radius_pos]) |>.mpr (by linarith))

end PoincareConjecture.MetricSurgeryResult

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

def centralClosedCollar : Set M := N.coordinate_map '' (univ ×ˢ Icc (-1 : ℝ) 1)

theorem inv_epsilon_gt_one : 1 < N.epsilon⁻¹ :=
  (one_lt_inv₀ N.epsilon_pos).mpr (N.epsilon_lt_half.trans (by norm_num))

theorem centralClosedCollar_compact : IsCompact N.centralClosedCollar := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  rintro z ⟨_, ha, hb⟩
  exact ⟨mem_univ _, by linarith [N.inv_epsilon_gt_one], by linarith [N.inv_epsilon_gt_one]⟩

theorem centralClosedCollar_subset : N.centralClosedCollar ⊆ N.carrier := by
  rintro x ⟨z, hz, rfl⟩
  exact MetricSurgery.neck_coordinate_mem N z
    ⟨mem_univ _, by linarith [N.inv_epsilon_gt_one, hz.2.1],
      by linarith [N.inv_epsilon_gt_one, hz.2.2]⟩

theorem centralBand_subset_closedCollar : N.region (-1) 1 ⊆ N.centralClosedCollar := by
  intro x hx
  exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
    MetricSurgery.neck_coordinate_inverse N hx.1⟩

theorem centralSphere_subset_band : N.central_sphere ⊆ N.region (-1) 1 := by
  intro x hx
  obtain ⟨hxN, hzero⟩ := (MetricSurgery.neck_central_iff N).mp hx
  exact ⟨hxN, by rw [hzero]; norm_num, by rw [hzero]; norm_num⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem isCompact_collapse_centralCollar :
    IsCompact (R.collapse '' I.neck.centralClosedCollar) :=
  I.neck.centralClosedCollar_compact.image_of_continuousOn
    (R.collapse_continuous.mono I.neck.centralClosedCollar_subset)

end PoincareConjecture.MetricSurgeryResult
