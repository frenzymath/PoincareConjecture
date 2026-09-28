import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.NormalCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.DiagonalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance interiorSourceConnected (k : ℕ) : ConnectedSpace (S.term k).carrier.carrier :=
  (S.term k).connectedSpace

theorem exists_complete_interior_geometric_limit
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S) :
    ∃ G : AncientPointedGeometricConvergence (fun k ↦ (S.term k).carrier)
        (fun k t ↦ (S.term k).flow.flow.metric (t - 1)) (fun k ↦ (S.term k).base) 1,
      G.limitCarrier.metricComplete (G.limitFlow.metric 0) := by
  classical
  let H := S.compactnessHypotheses P hcontrol
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1) le_rfl
  obtain ⟨σ, hσ, R, ρ, a, b, N, hparams, hcovers⟩ :=
    H.exists_diagonal_normalChartCovers (by norm_num)
  let seq := H.sequence.subsequence σ
  let selected : NormalizedKappaSolutionSequence kappa :=
    ⟨S.kappa_pos, fun k ↦ S.term (σ k)⟩
  have hselected : M23AllTimeCurvatureControl selected := by
    intro r hr
    obtain ⟨C, hC, hbound⟩ := hcontrol r hr
    exact ⟨C, hC, fun k ↦ hbound (σ k)⟩
  let cover : ∀ k j, j ≤ k → NormalChartCover (seq.flow k).flow.metric
      (seq.flow k).base (-1) 1 ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j) :=
    fun k j hjk ↦ (hcovers k j hjk).choose
  have hraw := RicciFlow.diagonal_referenceCharts_analytic_bounds_of_estimates
    (δ := 1) seq hparams cover (by
      intro j I hIcompact hI
      obtain ⟨l, hl⟩ := hIcompact.bddBelow
      let s := min (-1) (l - 1)
      have hs : s < 0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have htime : I ⊆ Ioo s 1 := by
        intro t ht
        exact ⟨lt_of_le_of_lt (min_le_right _ _) (by linarith [hl ht]), hI ht⟩
      let W := selected.compactnessHypotheses P hselected hs (by norm_num : (0 : ℝ) < 1) le_rfl
      have hA : 0 < (j : ℝ) + 1 := by positivity
      obtain ⟨a', b', ha', hb', helliptic⟩ :=
        W.eventually_referenceNormalChartCover_ellipticity H.time_bounds (N := N j)
          hA (hparams j).1 (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2
      refine ⟨s, a', htime, ha', ?_, ?_⟩
      · filter_upwards [helliptic] with k hk
        intro hjk i
        let cov : NormalChartCover (W.sequence.flow k).metricAt
            (W.sequence.flow k).base (-1) 1 ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j) :=
          cover k j hjk
        constructor
        · simpa only [cov, BasedFlow.metricAt, W, seq, H, selected,
            compactnessHypotheses, windowSequence, PointedFlowSequence.subsequence,
            BasedKappaSolution.basedWindow, BasedKappaSolution.shiftedWindowFlow,
            RicciFlow.translate] using W.referenceNormalChartCover_contDiffOn k cov i
        · intro t ht x hx v
          simpa only [cov, BasedFlow.metricAt, W, seq, H, selected,
            compactnessHypotheses, windowSequence, PointedFlowSequence.subsequence,
            BasedKappaSolution.basedWindow, BasedKappaSolution.shiftedWindowFlow,
            RicciFlow.translate] using (hk cov i t ht x hx v).1
      · intro d
        obtain ⟨B, _, hbound⟩ :=
          W.eventually_referenceNormalChartCover_spacetime_jet_bound_of_m23_predecessors
            P H.time_bounds hIcompact htime (N := N j)
            hA (hparams j).1 (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2 d
        exact ⟨B, hbound.mono fun k hk hjk ↦ hk (cover k j hjk)⟩)
  let Fseq (k : ℕ) : RicciFlow 3 (seq.carrier k).carrier
      ((fun t : ℝ ↦ t - 1) ⁻¹' Iic 0) :=
    (S.term (σ k)).flow.flow.bufferedExpandingFlow 1
  have htime : ∀ s t : ℝ, t < 1 → ∀ᶠ k : ℕ in atTop,
      Icc s t ⊆ (fun u : ℝ ↦ u - 1) ⁻¹' Iic 0 := by
    intro s t ht
    exact Eventually.of_forall fun k u hu ↦ by
      change u - 1 ≤ 0
      linarith [hu.2]
  obtain ⟨G, hG⟩ := NormalChartCover.exists_complete_ancient_geometric_limit
    Fseq (fun _ ↦ rfl) (by norm_num : (0 : ℝ) < 1) htime cover
    (fun j ↦ (hparams j).1) (fun j ↦ by linarith [(hparams j).1, (hparams j).2.1])
    (fun j ↦ (hparams j).2.2.1) hraw
  exact ⟨G.ofSubsequence hσ, hG⟩

end PoincareConjecture.NormalizedKappaSolutionSequence
