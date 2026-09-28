import PoincareConjecture.Proofs.M15.Lemma8_8_SliceTransfer
import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]

theorem actualBallCylinder_compact_slice_image_volume_le
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (t : (G.timeIntervals.interval K).Point)
    {V : Set C} (hV : IsCompact V) :
    calibratedMetricVolume (G.slices t.val).metricOnPoints
      (movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices t '' V) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (r⁻¹) ^ 2 * (T - t.val))) ^ n *
        calibratedMetricVolume (G.slices T).metricOnPoints (B.source_map '' V) := by
  obtain ⟨f, hf, hrecover, hbound⟩ := actualBallCylinder_exists_slice_transfer hM12 B t
  have hlocal : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ B.source_map := by
    rw [← actualBallCylinder_terminal_sliceMap_eq B]
    exact movingGaugeSliceMap_localDiffeomorph B.embedding.toMovingSpacetimeGauge
      G.slices B.metric.toMovingSpacetimeGaugeGeometry ⟨T, B.base_mem⟩
  have hU : IsOpen ((G.slices T).metricOnPoints.ball x r) := by
    rw [← B.source_map_range]
    exact hlocal.isOpen_range
  have hsub : B.source_map '' V ⊆ (G.slices T).metricOnPoints.ball x r := by
    rw [← B.source_map_range]
    exact image_subset_range _ _
  have himage : f '' (B.source_map '' V) =
      movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices t '' V := by
    rw [image_image]
    exact congrArg (fun m : C → (G.slices t.val).Point => m '' V) (funext hrecover)
  rw [← himage]
  exact calibratedMetricVolume_image_le_of_tangentNorm_le_on_compact
    (G.slices T).metricOnPoints (G.slices t.val).metricOnPoints hU
    (hV.image B.source_map_embedding.continuous) hsub (hf.of_le (by simp))
    (Real.exp_pos _) hbound

theorem actualBallCylinder_compact_slice_buffer
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (hcompact : IsCompact (closure ((G.slices T).metricOnPoints.ball x r)))
    (t : (G.timeIntervals.interval K).Point) :
    let A : Set C := {c | (G.slices T).metricOnPoints.edist x (B.source_map c) ≤
      ENNReal.ofReal (5 * r / 12)}
    IsCompact (movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices t '' A) ∧
      calibratedMetricVolume (G.slices t.val).metricOnPoints
        (movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices t '' A) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (r⁻¹) ^ 2 * (T - t.val))) ^ n *
        calibratedMetricVolume (G.slices T).metricOnPoints
          ((G.slices T).metricOnPoints.ball x r) := by
  intro A
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : (G.slices T).Point → Type _) :=
    ⟨(G.slices T).metricOnPoints.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : (G.slices T).Point → Type _) :=
    ⟨⟨(G.slices T).metricOnPoints.inner,
      (G.slices T).metricOnPoints.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace (G.slices T).Point :=
    .ofRiemannianMetric (𝓡 n) (G.slices T).Point
  have hfull : Metric.closedEBall x (ENNReal.ofReal (5 * r / 12)) ⊆
      (G.slices T).metricOnPoints.ball x r := by
    intro z hz
    change edist x z < ENNReal.ofReal r
    rw [edist_comm]
    exact (Metric.mem_closedEBall.mp hz).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff B.radius_pos).mpr (by linarith [B.radius_pos]))
  have hA : A = B.source_map ⁻¹' Metric.closedEBall x (ENNReal.ofReal (5 * r / 12)) := by
    ext c
    change edist x (B.source_map c) ≤ _ ↔ edist (B.source_map c) x ≤ _
    rw [edist_comm]
  have hAcompact : IsCompact A := by
    rw [hA]
    exact B.source_map_embedding.isInducing.isCompact_preimage'
      (hcompact.of_isClosed_subset Metric.isClosed_closedEBall (hfull.trans subset_closure))
      (by rw [B.source_map_range]; exact hfull)
  have hm := (movingGaugeSliceMap_localDiffeomorph B.embedding.toMovingSpacetimeGauge
    G.slices B.metric.toMovingSpacetimeGaugeGeometry t).contMDiff.continuous
  refine ⟨hAcompact.image hm, (actualBallCylinder_compact_slice_image_volume_le
    hM12 B t hAcompact).trans ?_⟩
  have hsub : B.source_map '' A ⊆ (G.slices T).metricOnPoints.ball x r := by
    rw [← B.source_map_range]
    exact image_subset_range _ _
  exact mul_le_mul' le_rfl (measure_mono hsub)

end PoincareConjecture.Proofs.M15
