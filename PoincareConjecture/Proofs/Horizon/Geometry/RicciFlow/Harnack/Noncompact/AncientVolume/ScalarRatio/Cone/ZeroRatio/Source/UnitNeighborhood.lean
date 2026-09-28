import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Family.OpenCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Quotient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.ConeTopology

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter Poincare.Gluing Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

theorem unitSlice_subset_iUnion_uniformBallRestriction
    {n : ℕ} {X : Type*} [MetricSpace X] {p : X}
    (hc : RayComparison p)
    (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r)
    (hbound : ∀ j (x v : EuclideanSpace ℝ (Fin n)),
      ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧ (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : ℕ → basedMinimizingRays p)
    (hdense : DenseRange (fun j =>
      asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))))
    (e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (hcenter : ∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ =
      asymptoticConeRayProjection hc (1, η j))
    (hcover : ∀ j, Metric.ball (e j ⟨0, Metric.mem_closedBall_self hr.le⟩) r ⊆ range (e j)) :
    {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆
      ⋃ j, range ((g j).uniformBallRestriction hr (e j)) := by
  intro z hz
  obtain ⟨j, hj⟩ := hdense.exists_dist_lt
    (⟨z, hz⟩ : AsymptoticConeUnitSlice p hc) (by positivity : 0 < r / 8)
  apply mem_iUnion.mpr
  refine ⟨j, (g j).ball_subset_range_uniformBallRestriction hr (hbound j) (e j) (he j)
    (hcover j) ?_⟩
  change dist z (e j ⟨0, Metric.mem_closedBall_self hr.le⟩) < r / 8
  rw [hcenter]
  exact hj

theorem exists_open_unitNeighborhood_of_normal_chart_family
    {n : ℕ} {X : Type*} [MetricSpace X] [ProperSpace X] {p : X}
    (hc : RayComparison p)
    (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r)
    (hbound : ∀ j (x v : EuclideanSpace ℝ (Fin n)),
      ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧ (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : ℕ → basedMinimizingRays p)
    (hdense : DenseRange (fun j =>
      asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))))
    (e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (hcenter : ∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ =
      asymptoticConeRayProjection hc (1, η j))
    (hcover : ∀ j, Metric.ball (e j ⟨0, Metric.mem_closedBall_self hr.le⟩) r ⊆ range (e j))
    (D : ℕ → ℕ → C(Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4) ×
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4), ℝ))
    (O : OverlapSystem (fun _ : ℕ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)))
    (hrel : ∀ i j x y, O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
    (hcross : ∀ i j x y,
      dist ((g i).uniformBallRestriction hr (e i) x) ((g j).uniformBallRestriction hr (e j) y) =
        D i j (x, y)) :
    ∃ f : Quotient O.setoid → AsymptoticCone p hc,
      Topology.IsOpenEmbedding f ∧
      (∀ j x, f (O.include j x) = (g j).uniformBallRestriction hr (e j) x) ∧
      range f = ⋃ j, range ((g j).uniformBallRestriction hr (e j)) ∧
      {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ range f ∧
      IsCompact (f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1}) := by
  let f := ChartDistance.quotientRealization O hrel
    (fun j => (g j).uniformBallRestriction hr (e j)) hcross
  have hopen : Topology.IsOpenEmbedding f :=
    ChartDistance.isOpenEmbedding_quotientRealization O hrel _ hcross
      (fun j => (g j).isOpenEmbedding_uniformBallRestriction hr (hbound j) (e j) (he j) (hcover j))
  have hrange : range f = ⋃ j, range ((g j).uniformBallRestriction hr (e j)) :=
    ChartDistance.range_quotientRealization O hrel _ hcross
  have hunit : {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ range f := by
    rw [hrange]
    exact unitSlice_subset_iUnion_uniformBallRestriction hc g hr hbound η hdense e he hcenter hcover
  exact ⟨f, hopen, (fun _ _ => rfl), hrange, hunit,
    hopen.isEmbedding.isInducing.isCompact_preimage'
      (isCompact_asymptoticCone_unit_slice hc) hunit⟩

theorem exists_isometric_unitNeighborhood_of_source_distance_limits
    {n : ℕ} {X : Type*} [MetricSpace X] [ProperSpace X] {p : X}
    (hc : RayComparison p)
    (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r)
    (hbound : ∀ j (x v : EuclideanSpace ℝ (Fin n)),
      ‖v‖ / 2 ≤ (g j).tangentNorm x v ∧ (g j).tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (η : ℕ → basedMinimizingRays p)
    (hdense : DenseRange (fun j =>
      asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))))
    (e : ∀ j, MetricCoordinateBall (g j) r → AsymptoticCone p hc)
    (he : ∀ j, Isometry (e j))
    (hcenter : ∀ j, e j ⟨0, Metric.mem_closedBall_self hr.le⟩ =
      asymptoticConeRayProjection hc (1, η j))
    (hcover : ∀ j, Metric.ball (e j ⟨0, Metric.mem_closedBall_self hr.le⟩) r ⊆ range (e j))
    {Y : ℕ → Type*} [∀ k, MetricSpace (Y k)]
    (source : ∀ k, ℕ → Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4) → Y k)
    (D : ℕ → ℕ → C(Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4) ×
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4), ℝ))
    (hD : ∀ i j x y, Tendsto (fun k => dist (source k i x) (source k j y))
      atTop (𝓝 (D i j (x, y))))
    (L : ℕ → ℝ≥0) (hupper : ∀ k j, LipschitzWith (L j) (source k j))
    (c : ℕ → ℝ) (hcpos : ∀ j, 0 < c j)
    (hlower : ∀ k j x y, c j * dist x y ≤ dist (source k j x) (source k j y))
    (hopen : ∀ k j, Topology.IsOpenEmbedding (source k j))
    (hconn : ∀ k (x : Y k) s, IsPreconnected (Metric.ball x s))
    (hcross : ∀ i j x y,
      dist ((g i).uniformBallRestriction hr (e i) x) ((g j).uniformBallRestriction hr (e j) y) =
        D i j (x, y)) :
    let A : ℕ → Type := fun _ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)
    let hne : ∀ j, Nonempty (A j) := fun _ => ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
    let hlocal : ∀ j, LocallyCompactSpace (A j) := fun _ => Metric.isOpen_ball.locallyCompactSpace
    let O := @ChartDistance.overlapSystem ℕ A (fun _ => inferInstance) hlocal hne
      Y inferInstance source D hD L hupper c hcpos hlower hopen hconn
    let hrel := @ChartDistance.overlapSystem_rel_iff ℕ A (fun _ => inferInstance) hlocal hne
      Y inferInstance source D hD L hupper c hcpos hlower hopen hconn
    letI := @ChartDistance.quotientMetricSpace ℕ A (fun _ => inferInstance) Y inferInstance
      source D hD O hrel hlocal L hupper c hcpos hlower hopen hconn
    ∃ f : Quotient O.setoid → AsymptoticCone p hc,
      Isometry f ∧ Topology.IsOpenEmbedding f ∧
      (∀ j x, f (O.include j x) = (g j).uniformBallRestriction hr (e j) x) ∧
      range f = ⋃ j, range ((g j).uniformBallRestriction hr (e j)) ∧
      {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1} ⊆ range f ∧
      IsCompact (f ⁻¹' {a : AsymptoticCone p hc | asymptoticConeRadius hc a = 1}) := by
  let A : ℕ → Type := fun _ => Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)
  let hne : ∀ j, Nonempty (A j) := fun _ => ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  let hlocal : ∀ j, LocallyCompactSpace (A j) := fun _ => Metric.isOpen_ball.locallyCompactSpace
  let O := @ChartDistance.overlapSystem ℕ A (fun _ => inferInstance) hlocal hne
    Y inferInstance source D hD L hupper c hcpos hlower hopen hconn
  let hrel := @ChartDistance.overlapSystem_rel_iff ℕ A (fun _ => inferInstance) hlocal hne
    Y inferInstance source D hD L hupper c hcpos hlower hopen hconn
  let := @ChartDistance.quotientMetricSpace ℕ A (fun _ => inferInstance) Y inferInstance
    source D hD O hrel hlocal L hupper c hcpos hlower hopen hconn
  obtain ⟨f, hfopen, hfinclude, hfrange, hfunit, hfcompact⟩ :=
    exists_open_unitNeighborhood_of_normal_chart_family hc g hr hbound η hdense
      e he hcenter hcover D O hrel hcross
  refine ⟨f, ?_, hfopen, hfinclude, hfrange, hfunit, hfcompact⟩
  apply Isometry.of_dist_eq
  intro q s
  induction q using Quotient.inductionOn with
  | h a =>
    induction s using Quotient.inductionOn with
    | h b =>
      change dist (f (O.include a.1 a.2)) (f (O.include b.1 b.2)) = D a.1 b.1 (a.2, b.2)
      rw [hfinclude, hfinclude]
      exact hcross a.1 b.1 a.2 b.2

end PoincareConjecture.RiemannianMetric
