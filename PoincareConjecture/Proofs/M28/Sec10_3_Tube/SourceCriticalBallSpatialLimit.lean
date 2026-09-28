import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallCurvature
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeNoncollapse
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallSourcePacket
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.GeometryLimit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

theorem exists_source_criticalBall_subsequence_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ {A1 : ℝ} (hA1 : 0 < A1),
          (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 ≤ A1 →
          (∀ r < A1, tube.eventuallyRadiusBound
            (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
            (fun k x => (H.tubeConnection T k).scalarCurvature x) r) →
          ∀ phi : ℕ → ℕ, StrictMono phi →
            Nonempty (RegularPointedMetricConvergence
              (fun k => H.tubeCriticalMetric T A1 (phi k))
              (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) := by
  classical
  obtain ⟨epsilonC, hCpos, hCsmall, hcurv⟩ :=
    exists_source_criticalBall_curvature_accuracy P
  obtain ⟨epsilonN, kappa, hNpos, _hNsmall, hkappa, hnoncollapse⟩ :=
    exists_source_tubeCritical_noncollapse_accuracy P
  refine ⟨min epsilonC epsilonN, lt_min hCpos hNpos,
    (min_le_left _ _).trans hCsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 hbase hcrit phi hphi
  let (k : ℕ) : PreconnectedSpace (H.tubeCriticalRegion T A1 k) :=
    (H.tubeCriticalRegion_connected T A1 hA1 k).toPreconnectedSpace
  let (k : ℕ) : MetricSpace (H.tubeCriticalRegion T A1 k) := by
    let g := H.tubeCriticalMetric T A1 k
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : H.tubeCriticalRegion T A1 k → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : H.tubeCriticalRegion T A1 k → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    letI : EMetricSpace (H.tubeCriticalRegion T A1 k) :=
      EMetricSpace.ofRiemannianMetric (𝓡 3) (H.tubeCriticalRegion T A1 k)
    exact EMetricSpace.toMetricSpace (fun x y => g.edist_ne_top x y)
  let D : ∀ k, LeviCivitaData (H.tubeCriticalMetric T A1 k) :=
    fun k => Classical.choice (exists_leviCivitaData (H.tubeCriticalMetric T A1 k))
  have heps : 0 < epsilon := by
    rw [← (T 0).epsilon_eq]
    exact (T 0).tube.epsilon_pos
  have hC : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hregular : 0 < ((4 * max C 2)⁻¹ * epsilon⁻¹ / 8) / 2 := by positivity
  obtain ⟨V, hV, hvolume⟩ := H.exists_tubeCritical_volume_bound T A1
  apply exists_regular_metric_limit_of_geometry
    (fun k => H.tubeCriticalMetric T A1 (phi k)) (fun k => D (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))
    (by norm_num) (fun _ _ _ => rfl) hregular (by norm_num : (0 : ℝ) < 1)
    hkappa hV.le
  · exact Eventually.of_forall (fun k =>
      H.tubeCritical_base_regular T A1 hA1 hbase (phi k))
  · exact Eventually.of_forall (fun k => hvolume (phi k))
  · exact Eventually.of_forall (fun k => hnoncollapse H T A1 hA1
      (hepsilon.trans (min_le_right _ _)) (phi k) (D (phi k)))
  · intro delta hdelta l
    obtain ⟨B, hB, hbound⟩ := hcurv H T
      (hepsilon.trans (min_le_left _ _)) hA1 D hcrit delta hdelta l
    exact ⟨B, hB, hphi.tendsto_atTop.eventually hbound⟩

theorem exists_source_criticalBall_spatial_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ {A1 : ℝ} (hA1 : 0 < A1),
          (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 ≤ A1 →
          (∀ r < A1, tube.eventuallyRadiusBound
            (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
            (fun k x => (H.tubeConnection T k).scalarCurvature x) r) →
          Nonempty (RegularPointedMetricConvergence
            (H.tubeCriticalMetric T A1) (H.tubeCriticalBase T A1 hA1)) := by
  obtain ⟨epsilon₀, hpos, hsmall, hgeometry⟩ :=
    exists_source_criticalBall_subsequence_limit_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 hbase hcrit
  exact hgeometry H T hepsilon hA1 hbase hcrit id strictMono_id

theorem exists_actual_source_criticalBall_spatial_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∃ W : CriticalBallSourcePacket H,
          Nonempty (RegularPointedMetricConvergence
            (H.tubeCriticalMetric W.tube W.radius)
            (H.tubeCriticalBase W.tube W.radius W.radius_pos)) := by
  obtain ⟨epsilonW, hWpos, _hWsmall, hpacket⟩ :=
    exists_criticalBall_source_packet_accuracy P
  obtain ⟨epsilonG, hGpos, hGsmall, hgeometry⟩ :=
    exists_source_criticalBall_spatial_limit_accuracy P
  refine ⟨min epsilonW epsilonG, lt_min hWpos hGpos,
    (min_le_right _ _).trans hGsmall, ?_⟩
  intro epsilon C A E H hepsilon
  obtain ⟨W⟩ := hpacket H (hepsilon.trans (min_le_left _ _))
  exact ⟨W, hgeometry H W.tube (hepsilon.trans (min_le_right _ _))
    W.radius_pos W.radius_lower W.radius_bound⟩

set_option maxHeartbeats 800000 in

theorem exists_actual_source_criticalBall_retained_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E), epsilon ≤ epsilon₀ →
        ∃ W : CriticalBallSourcePacket H,
          ∃ G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
            (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k)),
            sSup {r : ℝ | tube.eventuallyRadiusBound
              (fun k x => ((H.tubeMetric W.tube (W.high_index (G.subsequence k))).edist
                (H.tubeBase W.tube (W.high_index (G.subsequence k))) x).toReal)
              (fun k x => (H.tubeConnection W.tube
                (W.high_index (G.subsequence k))).scalarCurvature x) r} = W.radius := by
  obtain ⟨epsilonW, hWpos, _hWsmall, hpacket⟩ :=
    exists_criticalBall_source_packet_accuracy P
  obtain ⟨epsilonG, hGpos, hGsmall, hgeometry⟩ :=
    exists_source_criticalBall_subsequence_limit_accuracy P
  refine ⟨min epsilonW epsilonG, lt_min hWpos hGpos,
    (min_le_right _ _).trans hGsmall, ?_⟩
  intro epsilon C A E H hepsilon
  obtain ⟨W⟩ := hpacket H (hepsilon.trans (min_le_left _ _))
  obtain ⟨G⟩ := hgeometry H W.tube (hepsilon.trans (min_le_right _ _))
    W.radius_pos W.radius_lower W.radius_bound W.high_index W.high_index_strictMono
  refine ⟨W, G, ?_⟩
  exact tube.critical_radius_preserved_by_subsequence
    (fun k x => ((H.tubeMetric W.tube k).edist (H.tubeBase W.tube k) x).toReal)
    (fun k x => (H.tubeConnection W.tube k).scalarCurvature x)
    (φ := W.high_index) (ψ := G.subsequence) W.radius_pos
    W.radius_bound W.high_index_strictMono W.high_point
    (fun j => ⟨W.high_radius_upper j, W.high_scalar_lower j⟩) G.subsequence_strictMono

end PoincareConjecture.M28.CounterexampleNeckFamily

namespace PoincareConjecture.M28

theorem exists_counterexample_criticalBall_spatial_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) (T : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ (epsilon C A : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ → 0 < C →
        ∀ E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1),
          ∃ H : CounterexampleNeckFamily E,
            ∃ W : CounterexampleNeckFamily.CriticalBallSourcePacket H,
              Nonempty (RegularPointedMetricConvergence
                (H.tubeCriticalMetric W.tube W.radius)
                (H.tubeCriticalBase W.tube W.radius W.radius_pos)) := by
  obtain ⟨epsilonH, hHpos, _hHsmall, hfamily⟩ :=
    exists_counterexample_neck_family_accuracy P T
  obtain ⟨epsilonG, hGpos, hGsmall, hgeometry⟩ :=
    CounterexampleNeckFamily.exists_actual_source_criticalBall_spatial_limit_accuracy P
  refine ⟨min epsilonH epsilonG, lt_min hHpos hGpos,
    (min_le_right _ _).trans hGsmall, ?_⟩
  intro epsilon C A heps hepsilon hC E
  obtain ⟨H⟩ := hfamily epsilon C A heps
    (hepsilon.trans (min_le_left _ _)) hC E
  obtain ⟨W, hlimit⟩ := hgeometry H (hepsilon.trans (min_le_right _ _))
  exact ⟨H, W, hlimit⟩

end PoincareConjecture.M28
