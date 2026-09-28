import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.OpenTimeExtraction
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Assembly
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Complete
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.PointedExhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Window











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open PoincareConjecture.ChartDistance
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in



theorem exists_complete_reference_convergence_on_open_time
    {n : ℕ} {T' T : ℝ} (S : PointedFlowSequence n T' T)
    (hT : T' < 0 ∧ 0 < T)
    {W : Set ℝ} (hW : IsOpen W) (hWord : W.OrdConnected)
    (hwindow : Ioo T' T ⊆ W)
    {J : ℕ → Set ℝ}
    (Fseq : ∀ k, RicciFlow n (S.carrier k).carrier (J k))
    (hmetric : ∀ k, (Fseq k).metric = (S.flow k).flow.metric)
    (htime : ∀ a b : ℝ, Icc a b ⊆ W →
      ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (U : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (e : ∀ k i, Piece U i → (S.carrier k).carrier)
    (L : ℕ → ℝ≥0)
    (he : letI : ∀ k, MetricSpace (S.carrier k).carrier :=
        fun k => (S.carrier k).metricSpaceOf ((Fseq k).metric 0)
      ∀ k i, LipschitzWith (L i) (e k i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : letI : ∀ k, MetricSpace (S.carrier k).carrier :=
        fun k => (S.carrier k).metricSpaceOf ((Fseq k).metric 0)
      ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))
    (hb : letI : ∀ k, MetricSpace (S.carrier k).carrier :=
        fun k => (S.carrier k).metricSpaceOf ((Fseq k).metric 0)
      ∀ i j (x : Piece U i) (y : Piece U j), ∃ B : ℝ,
        ∀ k, dist (e k i x) (e k j y) ≤ B)
    {i₀ : ℕ} (q : Piece U i₀)
    (hbase : ∀ k, e k i₀ q = (S.flow k).base)
    (hcover : letI : ∀ k, MetricSpace (S.carrier k).carrier :=
        fun k => (S.carrier k).metricSpaceOf ((Fseq k).metric 0)
      ∀ R : ℝ, 0 < R → ∃ s : Finset ℕ, ∃ K : ∀ i, Set (Piece U i),
        (∀ i ∈ s, IsCompact (K i)) ∧
          ∀ᶠ k in atTop, ball (e k i₀ q) R ⊆ ⋃ i ∈ s, e k i '' K i)
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤ ((Fseq k).metric 0).pullbackCoefficients
          (chartParametrization U hU (e k i)) x v v)
    (hjets : ∀ i K, IsCompact K → K ⊆ W ×ˢ U i → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric z.1).pullbackCoefficients
            (chartParametrization U hU (e k i)) z.2) z‖ ≤ B)
    (hpositive : ∀ t ∈ W, ∀ i x, x ∈ U i → ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ v, a * ‖v‖ ^ 2 ≤ ((Fseq k).metric t).pullbackCoefficients
        (chartParametrization U hU (e k i)) x v v) :
    ∃ G : PointedGeometricConvergence S,
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
      ∃ F : RicciFlow n G.limitCarrier.carrier W,
        F.metric = G.limitFlow.flow.metric ∧
        G.limitCarrier.metricComplete (F.metric 0) ∧
        ∀ q' : G.limitCarrier.carrier, ∀ m : ℕ,
          ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
          K ⊆ W ×ˢ (extChartAt (𝓡 n) q').target → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m
              (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
                ((Fseq (G.subsequence k)).metric z.1).pullbackCoefficients
                  ((fun x => ((G.embedding k).toFun (0, x)).2) ∘
                    (extChartAt (𝓡 n) q').symm) z.2))
            (iteratedFDeriv ℝ m
              (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
                (F.metric z.1).pullbackCoefficients
                  (extChartAt (𝓡 n) q').symm z.2)) atTop K := by
  classical
  let : ∀ k, MetricSpace (S.carrier k).carrier :=
    fun k => (S.carrier k).metricSpaceOf ((Fseq k).metric 0)
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  have hconn : ∀ k (x : (S.carrier k).carrier) r, IsPreconnected (ball x r) := by
    intro k x r
    rw [FlowCarrier.metricBall_eq_metricBallOf]
    exact ((Fseq k).metric 0).isPreconnected_ball x r
  obtain ⟨ρ, hρ, B, hBsmooth, hBjets, D, hD, hbound, g, hcompat,
      F, hF, hcoeff, _hquotientJets⟩ :=
    exists_quotientFlow_of_controlled_charts_on_open_time U hU e L he c hc hlower
      hopen hconn hsmooth hb hW hWord (hwindow hT) Fseq htime helliptic hjets hpositive
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
  have htime' : ∀ a b : ℝ, Icc a b ⊆ W →
      ∀ᶠ k in atTop, Icc a b ⊆ J (ρ (σ k)) :=
    fun a b hab => (hρ.comp hσ).tendsto_atTop.eventually (htime a b hab)
  have hsourceJets : ∀ i m K, IsCompact K → K ⊆ W ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq (ρ (σ k))).metric z.1).pullbackCoefficients
            (chartParametrization U hU (f k ∘ O.include i)) z.2))
      (iteratedFDeriv ℝ m (B i)) atTop K := by
    apply source_exhaustion_spacetime_pullbackCoefficients_tendsto_jets U hU O hO
      hE hEmono hEcover f (fun k => (hf k).2.1)
      L (fun k => he (ρ (σ k))) c hc (fun k => hlower (ρ (σ k)))
      (fun k => hopen (ρ (σ k))) (fun k => hconn (ρ (σ k)))
      (fun k => hsmooth (ρ (σ k))) happrox hreadout
      W hW (fun k => (Fseq (ρ (σ k))).metric) B hBsmooth ?_
      (fun i m K hK hKU V hV =>
        hσ.tendsto_atTop.eventually (hBjets i m K hK hKU V hV))
    intro i z hz
    obtain ⟨a, b, _, habnhds, habW⟩ :=
      exists_Icc_mem_subset_of_mem_nhds (hW.mem_nhds hz.1)
    have hab : z.1 ∈ Ioo a b := Icc_mem_nhds_iff.mp habnhds
    refine ⟨Ioo a b ×ˢ U i, isOpen_Ioo.prod (hU i), ⟨hab, hz.2⟩, ?_⟩
    filter_upwards [htime' a b habW] with k hk
    exact contDiffOn_source_chart_spacetime_pullbackCoefficients U hU
      (hsmooth (ρ (σ k)) i).contMDiff
      ((Fseq (ρ (σ k))).smooth.mono
        (prod_mono (Ioo_subset_Icc_self.trans hk) (Subset.refl _))) isOpen_Ioo
  let C := O.flowCarrier U hU hO hclosed
  let Fref : BasedFlow n T' T C :=
    C.basedWindow F (O.include i₀ q) hwindow (hT.1.trans hT.2)
  have hreferenceJets : ∀ i m K, IsCompact K → K ⊆ Ioo T' T ×ˢ U i →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((S.flow (ρ (σ k))).flow.metric z.1).pullbackCoefficients
              (chartParametrization U hU (f k ∘ O.include i)) z.2))
        (iteratedFDeriv ℝ m (B i)) atTop K := by
    intro i m K hK hKU
    simpa only [hmetric] using hsourceJets i m K hK
      (hKU.trans (prod_mono hwindow (Subset.refl _)))
  let G0 := pointedGeometricConvergence_of_quotient_limit U hU O hO hclosed
    (fun k => S.flow (ρ (σ k))) Fref g hcompat hF hE hEc hEK hEmono hEcover
    f (fun k => (hf k).1) (fun k => (hf k).2.1) hEp
    (fun k => (hf k).2.2.trans (hbase (ρ (σ k)))) B
    (fun i => (hBsmooth i).continuousOn.mono (prod_mono hwindow (Subset.refl _)))
    (fun t ht => hcoeff t (hwindow ht)) hreferenceJets
  have hcomplete : C.metricComplete (F.metric 0) := by
    apply G0.metricComplete_zero_of_boundary_escape hT
    intro A hA
    obtain ⟨j, hj⟩ := hescape A hA
    refine ⟨j, hj.mono fun k hk x hx => ?_⟩
    have h := hk x hx
    rw [hbase (ρ (σ k))] at h
    change ENNReal.ofReal A ≤
      ((S.carrier (ρ (σ k))).metricEMetricSpace ((Fseq (ρ (σ k))).metric 0)).edist
        (S.flow (ρ (σ k))).base (f k x) at h
    rw [congrArg (fun metric => metric 0) (hmetric (ρ (σ k)))] at h
    exact h
  let G : PointedGeometricConvergence S := G0.reindex (hρ.comp hσ)
  refine ⟨G, F, rfl, hcomplete, ?_⟩
  intro q' m K hK hKchart
  obtain ⟨i, _, htarget, hinverse⟩ := exists_chosen_quotient_chart U hU O q'
  have hKU : K ⊆ W ×ˢ U i := by
    simpa only [htarget] using hKchart
  have hlimit : EqOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q').symm z.2)
      (B i) (W ×ˢ U i) := by
    rw [hF, hinverse]
    exact quotientMetric_family_pullbackCoefficients_eqOn U hU O hO
      (fun i t => g t i) hcompat B hcoeff i
  have hsource (k : ℕ) := chosenChart_spacetime_pullbackCoefficients_iteratedFDeriv_eq
    U hU O q' i hinverse (Fseq (ρ (σ k))).metric (fun _ => f k) m
  apply ((hsourceJets i m K hK hKU).congr ?_).congr_right ?_
  · exact Eventually.of_forall fun k p _ => congrFun (hsource k).symm p
  · intro p hp
    exact ((eqOn_iteratedFDeriv_of_isOpen (hW.prod (hU i)) hlimit m) (hKU hp)).symm

end PoincareConjecture.M30
