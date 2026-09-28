import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.Extraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.GeometricLimit.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.PointedExhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.SourceMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {n : ℕ} (C : ℕ → FlowCarrier.{0} n)

local instance ancientGeometric_sourceTopology (k : ℕ) :
    TopologicalSpace (C k).carrier := (C k).topologicalSpace
local instance ancientGeometric_sourceCharts (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (C k).carrier :=
  (C k).chartedSpace
local instance ancientGeometric_sourceManifold (k : ℕ) :
    IsManifold (𝓡 n) ∞ (C k).carrier := (C k).isManifold

variable {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (C k).carrier (J k))

theorem exists_complete_ancient_geometric_limit_of_controlled_charts
    (p : ∀ k, (C k).carrier) {T : ℝ} (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (e : ∀ k i, Piece U i → (C k).carrier)
    (L : ℕ → ℝ≥0)
    (he : letI : ∀ k, MetricSpace (C k).carrier :=
        fun k => (C k).metricSpaceOf ((Fseq k).metric 0)
      ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : letI : ∀ k, MetricSpace (C k).carrier :=
        fun k => (C k).metricSpaceOf ((Fseq k).metric 0)
      ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hb : letI : ∀ k, MetricSpace (C k).carrier :=
        fun k => (C k).metricSpaceOf ((Fseq k).metric 0)
      ∀ i j (x : Piece U i) (y : Piece U j), ∃ B : ℝ,
      ∀ k, dist (e k i x) (e k j y) ≤ B)
    {i₀ : ℕ} (q : Piece U i₀) (hbase : ∀ k, e k i₀ q = p k)
    (hcover : letI : ∀ k, MetricSpace (C k).carrier :=
        fun k => (C k).metricSpaceOf ((Fseq k).metric 0)
      ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e k i₀ q) R ⊆ ⋃ i ∈ s, e k i '' K i)
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((Fseq k).metric 0).pullbackCoefficients
          (chartParametrization U hU (e k i)) x v v)
    (hjets : ∀ i K, IsCompact K → K ⊆ Iio T ×ˢ U i → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients
            (chartParametrization U hU (e k i)) z.2) z‖ ≤ B)
    (hpositive : ∀ t ∈ Iio T, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤ ((Fseq k).metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)) x v v) :
    ∃ G : AncientPointedGeometricConvergence C (fun k => (Fseq k).metric) p T,
      letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      G.limitCarrier.metricComplete (G.limitFlow.metric 0) := by
  let : ∀ k, MetricSpace (C k).carrier :=
    fun k => (C k).metricSpaceOf ((Fseq k).metric 0)
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  have hconn : ∀ k (x : (C k).carrier) r, IsPreconnected (ball x r) := by
    intro k x r
    rw [FlowCarrier.metricBall_eq_metricBallOf]
    exact ((Fseq k).metric 0).isPreconnected_ball x r
  obtain ⟨ρ, hρ, B, hBsmooth, hBjets, D, hD, hbound, g, hcompat, F, hF, hcoeff⟩ :=
    exists_ancient_quotientRicciFlow_of_controlled_charts U hU e L he c hc hlower
      hopen hconn hsmooth hb hT Fseq htime helliptic hjets hpositive
  let hp := fun i j x y => (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := overlapSystem hp L (fun k => he (ρ k)) c hc (fun k => hlower (ρ k))
    (fun k => hopen (ρ k)) (fun k => hconn (ρ k))
  let hO := overlapSystem_smooth U hU hp L (fun k => he (ρ k)) c hc
    (fun k => hlower (ρ k)) (fun k => hopen (ρ k)) (fun k => hconn (ρ k))
    (fun k => hsmooth (ρ k)) hbound
  let hclosed := overlapSystem_closed hp L (fun k => he (ρ k)) c hc
    (fun k => hlower (ρ k)) (fun k => hopen (ρ k)) (fun k => hconn (ρ k))
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have hcover' : ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
      (∀ i ∈ s, IsCompact (K i)) ∧
        ∀ᶠ k in atTop, ball (e (ρ k) i₀ q) R ⊆ ⋃ i ∈ s, e (ρ k) i '' K i := by
    intro R hR
    obtain ⟨s, K, hK, hcov⟩ := hcover R hR
    exact ⟨s, K, hK, hρ.tendsto_atTop.eventually hcov⟩
  obtain ⟨hconnected, E, hE, hEc, hEp, hEK, hEstep, hEcover, σ, hσ,
      f, hf, happrox, hreadout, hescape⟩ :=
    exists_pointed_source_exhaustion_with_boundary_escape U hU hD L
      (fun k => he (ρ k)) c hc (fun k => hlower (ρ k)) (fun k => hopen (ρ k))
      (fun k => hconn (ρ k)) (fun k => hsmooth (ρ k)) hbound q hcover'
  let : ConnectedSpace (Quotient O.setoid) := hconnected
  have hEmono : Monotone E := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hEstep j)
  have htime' : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J (ρ (σ k)) :=
    fun a b hb => (hρ.comp hσ).tendsto_atTop.eventually (htime a b hb)
  have hsourceJets := source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets_of_expanding_flows
    U hU O hO hE hEmono hEcover f (fun k => (hf k).2.1)
    L (fun k => he (ρ (σ k))) c hc (fun k => hlower (ρ (σ k)))
    (fun k => hopen (ρ (σ k))) (fun k => hconn (ρ (σ k))) (fun k => hsmooth (ρ (σ k)))
    happrox hreadout (fun k => Fseq (ρ (σ k))) htime' B hBsmooth
    (fun i m K hK hKU V hV => hσ.tendsto_atTop.eventually (hBjets i m K hK hKU V hV))
  let G := completeAncientConvergence (fun k => C (ρ (σ k))) U hU O hO hclosed hT
    (fun k => Fseq (ρ (σ k))) (fun k => p (ρ (σ k))) htime' F (O.include i₀ q)
    g hcompat hF hE hEc hEK hEmono hEcover f (fun k => (hf k).1)
    (fun k => (hf k).2.1) hEp (fun k => (hf k).2.2.trans (hbase (ρ (σ k))))
    B (fun i => (hBsmooth i).continuousOn) hcoeff hsourceJets (by
      intro A hA
      obtain ⟨j, hj⟩ := hescape A hA
      refine ⟨j, hj.mono fun k hk x hx => ?_⟩
      have h := hk x hx
      rw [hbase (ρ (σ k))] at h
      exact h)
  exact ⟨G.val.ofSubsequence (hρ.comp hσ), G.property⟩

end PoincareConjecture.ChartDistance
