import PoincareConjecture.Proofs.M47.LimitFiniteSliceJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

private theorem physical_ball_transport
    (F : SurgeryFlowData.{u}) {p q : (t : ℝ) × (F.slice t).carrier}
    (hpq : p = q) {r : ℝ} (y : (F.slice q.1).carrier)
    (hy : y ∈ (F.metric q.1).ball q.2 r) :
    ∃ z ∈ (F.metric p.1).ball p.2 r,
      (⟨p.1, z⟩ : (t : ℝ) × (F.slice t).carrier) = ⟨q.1, y⟩ := by
  cases hpq
  exact ⟨y, hy, rfl⟩

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {J : Set ℝ} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges) J)

private local instance endpointCaptureTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance endpointCaptureCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance endpointCaptureManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold



theorem limitFinite_terminal_physical_ball_capture
    (P : M47Predecessors.{u}) {R : ℝ} (hR : 0 < R) :
    ∃ j : ℕ, ∀ᶠ k : ℕ in atTop,
      G.exhaustion.space j ⊆ G.exhaustion.space k ∧
      ∀ y ∈ ((F (G.subsequence k)).metric (baseTime (G.subsequence k))).ball
          ((history (G.subsequence k)).history.forward (baseTime (G.subsequence k))
            (hbaseTime (G.subsequence k)) (basePoint (G.subsequence k)))
          (R / Real.sqrt ((V).scale (G.subsequence k))),
        ∃ x ∈ G.exhaustion.space j,
          (⟨limitFinitePhysicalSliceTime G 0 k,
              limitFinitePhysicalSliceChart G F (fun i => (history i).history) 0 k x⟩ :
            (t : ℝ) × ((F (G.subsequence k)).slice t).carrier) =
              ⟨baseTime (G.subsequence k), y⟩ := by
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let phi := fun k => limitFinitePhysicalSliceChart G F (fun i => (history i).history) 0 k
  let g := fun k => rescaledMetric
    ((F (G.subsequence k)).metric (limitFinitePhysicalSliceTime G 0 k))
    ((V).scale (G.subsequence k)) ((V).base_scalar_pos (G.subsequence k))
  obtain ⟨j, hj⟩ := terminalCurvature_source_balls_of_original_jets
    g (G.limit.flow.metric 0) (G.limit.complete 0 G.limit.zero_mem)
    G.exhaustion.space G.exhaustion.space_open G.exhaustion.space_increasing
    G.exhaustion.space_covers phi
    (limitFinite_physical_slice_chart_source G F (fun i => (history i).history) 0)
    (fun q : G.limit.sliceCarrier.carrier => limitCanonicalNativeChart q)
    (fun x => ⟨x, mem_extChartAt_source x⟩)
    (fun q _ hK hKc => limitFinite_physical_slice_coefficient_jets G P F
      (fun i => (history i).history) 0 G.limit.zero_mem q 0 hK hKc)
    G.limit.base hR
  refine ⟨j, ?_⟩
  filter_upwards [hj, eventually_ge_atTop j] with k hk hjk
  refine ⟨G.exhaustion.space_increasing hjk, ?_⟩
  have hzero : limitFiniteSliceTime G 0 k = 0 := by simp [limitFiniteSliceTime]
  have hpoint : (G.embedding k).pointMap (limitFiniteSliceTime G 0 k)
      (limitFinite_slice_time_mem G 0 k) G.limit.base = (V).base (G.subsequence k) := by
    simpa only [hzero] using G.base_preserving k
      ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have hcenter := limitCanonicalPhysicalChart_point_identity (G.embedding k)
    (G.exhaustion.space_open k) (history (G.subsequence k)).history
    (limitFiniteSliceTime G 0 k) (limitFinite_slice_time_mem G 0 k)
    (limitFinite_physical_slice_time_mem G 0 k) G.limit.base
    ((V).base (G.subsequence k)) (hbaseTime (G.subsequence k)) hpoint
  intro y hy
  obtain ⟨z, hz, hzy⟩ := physical_ball_transport (F (G.subsequence k)) hcenter y hy
  have hzscaled : z ∈ (g k).ball (phi k G.limit.base) R := by
    have hsqrt : 0 < Real.sqrt ((V).scale (G.subsequence k)) :=
      Real.sqrt_pos.mpr ((V).base_scalar_pos (G.subsequence k))
    have hne := (ENNReal.ofReal_pos.mpr hsqrt).ne'
    change (rescaledMetric _ _ _).edist _ z < ENNReal.ofReal R
    rw [rescaledMetric_edist]
    change _ < ENNReal.ofReal (R / Real.sqrt ((V).scale (G.subsequence k))) at hz
    rw [ENNReal.ofReal_div_of_pos hsqrt] at hz
    simpa only [phi, limitFinitePhysicalSliceChart, limitFinitePhysicalSliceTime, mul_comm] using
      (ENNReal.lt_div_iff_mul_lt (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).mp hz
  obtain ⟨x, hx, hxz⟩ := hk hzscaled
  refine ⟨x, hx, ?_⟩
  exact (congrArg (fun z =>
    (⟨limitFinitePhysicalSliceTime G 0 k, z⟩ :
      (t : ℝ) × ((F (G.subsequence k)).slice t).carrier)) hxz).trans hzy

end PoincareConjecture.M47
