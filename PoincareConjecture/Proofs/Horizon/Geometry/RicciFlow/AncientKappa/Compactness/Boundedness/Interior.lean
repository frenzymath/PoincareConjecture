import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.NormalCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.DiagonalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance interiorCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)



theorem exists_complete_interior_geometric_limit
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : AncientPointedGeometricConvergence C
        (fun k t => (F k).metric (t - δ)) p δ,
      G.limitCarrier.metricComplete (G.limitFlow.metric 0) := by
  classical
  let H := compactnessHypotheses C F p P hκ hc hop hnc L hL hbound
    (by norm_num : (-1 : ℝ) < 0) hδ le_rfl
  obtain ⟨σ, hσ, R, ρ, a, b, N, hparams, hcovers⟩ :=
    H.exists_diagonal_normalChartCovers (by norm_num)
  let seq := H.sequence.subsequence σ
  let cover : ∀ k j, j ≤ k → NormalChartCover (seq.flow k).flow.metric
      (seq.flow k).base (-1) δ ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j) :=
    fun k j hjk => (hcovers k j hjk).choose
  have hraw := RicciFlow.diagonal_referenceCharts_analytic_bounds_of_estimates
    (δ := δ) seq hparams cover (by
      intro j I hIcompact hI
      obtain ⟨l, hl⟩ := hIcompact.bddBelow
      let s := min (-1) (l - 1)
      have hs : s < 0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have htime : I ⊆ Ioo s δ := by
        intro t ht
        exact ⟨lt_of_le_of_lt (min_le_right _ _) (by linarith [hl ht]), hI ht⟩
      let W := compactnessHypotheses (fun k => C (σ k)) (fun k => F (σ k))
        (fun k => p (σ k)) P hκ (fun k => hc (σ k)) (fun k => hop (σ k))
        (fun k => hnc (σ k)) (fun k => L (σ k)) (hL.comp hσ.tendsto_atTop)
        (fun k => hbound (σ k)) hs hδ le_rfl
      have hA : 0 < (j : ℝ) + 1 := by positivity
      obtain ⟨a', b', ha', hb', helliptic⟩ :=
        W.eventually_referenceNormalChartCover_ellipticity H.time_bounds (N := N j)
          hA (hparams j).1 (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2
      refine ⟨s, a', htime, ha', ?_, ?_⟩
      · filter_upwards [helliptic] with k hk
        intro hjk i
        let cov : NormalChartCover (W.sequence.flow k).metricAt
            (W.sequence.flow k).base (-1) δ ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j) :=
          cover k j hjk
        constructor
        · simpa only [cov, BasedFlow.metricAt, W, seq, H,
            compactnessHypotheses, windowSequence, PointedFlowSequence.subsequence,
            basedWindow, shiftedWindowFlow, RicciFlow.translate] using
            W.referenceNormalChartCover_contDiffOn k cov i
        · intro t ht x hx v
          simpa only [cov, BasedFlow.metricAt, W, seq, H,
            compactnessHypotheses, windowSequence, PointedFlowSequence.subsequence,
            basedWindow, shiftedWindowFlow, RicciFlow.translate] using (hk cov i t ht x hx v).1
      · intro d
        obtain ⟨B, _, hjet⟩ :=
          W.eventually_referenceNormalChartCover_spacetime_jet_bound_of_m23_predecessors
            P H.time_bounds hIcompact htime (N := N j)
            hA (hparams j).1 (hparams j).2.1 (hparams j).2.2.1 (hparams j).2.2.2 d
        exact ⟨B, hjet.mono fun k hk hjk => hk (cover k j hjk)⟩)
  let Fseq (k : ℕ) : RicciFlow 3 (seq.carrier k).carrier
      ((fun t : ℝ => t - δ) ⁻¹' Iic 0) :=
    (F (σ k)).bufferedExpandingFlow δ
  have htime : ∀ s t : ℝ, t < δ → ∀ᶠ k : ℕ in atTop,
      Icc s t ⊆ (fun u : ℝ => u - δ) ⁻¹' Iic 0 := by
    intro s t ht
    exact Eventually.of_forall fun k u hu => by
      change u - δ ≤ 0
      linarith [hu.2]
  obtain ⟨G, hG⟩ := NormalChartCover.exists_complete_ancient_geometric_limit
    Fseq (fun _ => rfl) hδ htime cover
    (fun j => (hparams j).1) (fun j => by linarith [(hparams j).1, (hparams j).2.1])
    (fun j => (hparams j).2.2.1) hraw
  exact ⟨G.ofSubsequence hσ, hG⟩



theorem exists_complete_bounded_interior_geometric_limit
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : AncientPointedGeometricConvergence C
        (fun k t => (F k).metric (t - δ)) p δ,
      (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
      (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).curvatureTensorNorm x ≤ 4) ∧
      ∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).NonnegativeCurvatureOperator x := by
  obtain ⟨G, hcomplete⟩ :=
    exists_complete_interior_geometric_limit C F p P hκ hc hop hnc L hL hbound hδ
  let Fseq (k : ℕ) := (F k).bufferedExpandingFlow δ
  have htime : ∀ a b : ℝ, b < δ → ∀ᶠ k : ℕ in atTop,
      Icc a b ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 := by
    intro a b hb
    exact Eventually.of_forall fun k t ht => by
      change t - δ ≤ 0
      linarith [ht.2]
  have hnorm : ∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).curvatureTensorNorm x ≤ 4 := by
    apply G.curvatureTensorNorm_le_of_uniform_ball_bound Fseq hδ htime
    intro a b hb r _
    filter_upwards [hL.eventually_ge_atTop r] with k hk t ht x hx
    have ht0 : t - δ ≤ 0 := by linarith [ht.2]
    have hx0 := ball_subset_terminal C F P hop k (t - δ) ht0 (p k) r hx
    exact (le_abs_self _).trans
      (hbound k (t - δ) ht0 x (hx0.trans_le (ENNReal.ofReal_le_ofReal hk)))
  refine ⟨G, RicciFlow.metricComplete_of_ancient_uniform_curvature_bound G.limitCarrier
    hδ G.limitFlow G.base hcomplete (by norm_num) hnorm, hnorm, ?_⟩
  apply G.nonnegativeCurvatureOperator_of_eventually Fseq hδ htime
  intro t ht
  exact Eventually.of_forall fun k x => hop k (t - δ) (by
    have h : t < δ := ht
    linarith) x

end PoincareConjecture.RawAncientSequence
